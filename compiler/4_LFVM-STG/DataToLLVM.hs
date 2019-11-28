{-# LANGUAGE OverloadedStrings, NoMonomorphismRestriction, StrictData
#-}

module DataToLLVM
where
-- Local imports
import StgSyn
import CodegenRuntime
import LlvmHsExts (globalStringPtr, constZero, charPtrType, unknownPtrType, sizeof)

-- LLVM
import LLVM.IRBuilder.Module
import LLVM.IRBuilder.Monad
import LLVM.IRBuilder.Instruction hiding (globalStringPtr)
import LLVM.AST hiding (function)
import LLVM.AST.Type as AST
import qualified LLVM.AST.Float as F
import qualified LLVM.AST.Constant as C
--import qualified LLVM.AST.IntegerPredicate as P
--import qualified LLVM.AST.FloatingPointPredicate as Pf
import LLVM.AST.Global
import LLVM.AST.Linkage
import LLVM.AST.Typed
import LLVM.AST.AddrSpace
import LLVM.AST.Attribute

-- ultra cancerous shortbytestrings
import qualified Data.ByteString.Short as BS
import qualified Data.ByteString.Char8 -- Char -> Word8

import Data.List (elemIndex) -- to match deconstruction orders
import qualified Data.Map.Strict as Map
import Control.Monad.State
import Control.Monad.Fix (MonadFix)
import Data.Functor
import Data.Functor.Identity (Identity)

import Debug.Trace
import Control.Exception (assert)

-- Memory management:
-- Stack frames are responsible for all data returned by functions they call !
-- The stack size needed is static and is sort of calculated anyway during codegen:
-- Recursive/lazy data must in general be on the heap:
-- stack frames are as before responsible for them and must call their destructors.
-- alloca memory obviously expires automatically as a function returns

-- Complications occur when we try to inline (non-lazy) sub-data,
-- since the sub-data might outlive the parent data

-- getType: get an llvm type from an StgType
getType :: CodeGenModuleConstraints m => StgType -> m LLVM.AST.Type
getType = \case
  StgLlvmType t   -> pure t
  StgTyperef t t2 -> pure t
  StgTypeAlias iden -> (gets (aliasToType iden . typeMap)) >>=
    maybe (error $ "unknown type: " ++ show iden) getType
-- used only by gen constructors
  StgAlgType stgData@(StgSumType iden alts) -> do
    conInfo <- gets (aliasToType iden . typeMap)
    case conInfo of
      Just (StgLlvmType ty) -> return ty
      Nothing -> genConstructor stgData *> getType (StgAlgType (StgSumType iden alts))
--   used only by fnToLlvm
  StgFnType types -> do
    llvmTypes <- mapM getType types
    let (argTypes, [retType]) = splitAt (length llvmTypes - 1) llvmTypes
        isVarArg = False
        fnType = FunctionType retType argTypes isVarArg
        fnPtr = PointerType fnType (AddrSpace 0)
    return fnPtr
  StgPApTy t1s t2s -> do
    fnType <- getType $ StgFnType $ t1s ++ t2s
    llvmTypes <- mapM getType t1s
    let papTy = StructureType False $ fnType : llvmTypes
    pure $ (`PointerType` (AddrSpace 0)) papTy
--StgTuple tys -> -- getOrMakeTuple tys >>= \(DataFns s f [] n) -> pure f

-- Resolves type aliases (also check for alias loops)
aliasToType :: StgId -> TypeMap -> Maybe StgType
aliasToType iden tMap = go iden tMap []
  where go iden map aliases = (Map.!? iden) tMap >>= \case -- Maybe monad
            StgTypeAlias nm -> if iden `elem` aliases
                               then Nothing
                               else go nm tMap (iden : aliases)
            any             -> return any

getOrMakeTuple ::  CodeGenIRConstraints m --CodeGenModuleConstraints m
  => [LLVM.AST.Type] -> m DataFns
getOrMakeTuple tys = gets ((tys `Map.lookup`) . tupleMap) >>= \case
  Just t  -> pure t
  Nothing -> do
    prodNm <- freshName ".Tuple"
    let prodTy = (StgProductType prodNm (StgLlvmType <$> tys))
    f <- genProductConstructor prodTy Nothing
    dataFn <- gets ((prodNm `Map.lookup`) . dataFnsMap) <&> \case
      Just df -> df
      Nothing -> error "panic: tuple didn't generate"
    modify (\x->x{ tupleMap=Map.insert tys dataFn (tupleMap x)})
    pure dataFn

-- **********************
-- * DataFns generation *
-- **********************
-- genConstructor
-- In general: productTypes -> struct ; sumTypes -> tag + void* pointer
-- Data is written to the (usually inAlloca) arg given.
-- Recursive data calls malloc
genConstructor :: CodeGenModuleConstraints m  => StgData -> m Operand
genConstructor = genSumConstructor

-- Product types need to call the sum constructor to become 'embedded' in the sum type
-- embedded product types have the same type as the outer sum constructor.
data InSumType = InSumType
 { sumConFn  :: StgFn         -- sumtype Constructor Function
 , tagNumber :: StgSsa        -- tag number for this product type
 , sumType   :: LLVM.AST.Type -- return type (of sumConFn, since we must tail call that)
 }

-- Generate the constructor function
-- These may require dynamic memory, in which case they also get a destructor
genProductConstructor :: CodeGenModuleConstraints m 
  => StgProductType -> Maybe InSumType -> m Operand
genProductConstructor algData@(StgProductType name fields) sumConstructor = do
  types <- mapM getType fields
  let productType = StructureType { isPacked = False, elementTypes = types }
      structName = name ; conFnName = name

  -- make a new typedef or use the sumtype if we're in one
  structType <- case sumConstructor of
      Nothing -> typedef name (Just productType)
      Just (InSumType conFn tag sumType) -> return sumType
  let sz = sizeof structType
      retType = PointerType structType (AddrSpace 0)
      subType  = PointerType productType (AddrSpace 0)
      deCon = StgTyperef retType subType
  modify (\x->x { typeMap = Map.insert name deCon (typeMap x) })

  -- generate llvm constructor function or global constant if empty (within a sumtype)
  -- if empty product type (within a sum type) -> make a global constant, not a function.
  let memberParams = (, ParameterName "A") <$> types
      genCon [] = case sumConstructor of
          Nothing -> error "empty product type" -- only legal within sumtypes, eg. `Nothing`
          Just (InSumType conFn tag sumType) -> do -- empty sum alts are basically variables
             let val = C.Struct Nothing False [C.Int 32 0, C.Null charPtrType]
             g <- global structName sumType (C.BitCast val sumType)
             modify (\x->x { bindMap = Map.insert name (ContLi g) (bindMap x) })
             return g

      genCon _ = -- generate constructor function (always starts with memory in which to write)
        let params = (charPtrType, "mem") : memberParams
            fnBody (mem : conArgs) = do
              structPtr <- bitcast mem retType
              let fillProduct prodPtr = zipWithM_ storeVal conArgs [0..]
                   where storeVal ssa idx = gep prodPtr [constZero, ConstantOperand $ C.Int 32 idx]
                           >>= \ptr -> store ptr 0 ssa
              case sumConstructor of
                  Nothing -> fillProduct structPtr *> ret structPtr
                  Just (InSumType conFn tag sumType) -> do
                     -- prodMem <- bitcast structPtr (PointerType (IntegerType 8) (AddrSpace 0))
                     prodMem <- gets ((\(Just (ContFn m))->m) . (Map.!? "malloc") . bindMap) >>=
                        \malloc -> call malloc [(ConstantOperand sz, [])]
                     prodPtr <- bitcast prodMem subType
                     fillProduct prodPtr
                     voidPtr <- bitcast prodPtr charPtrType
                     ret =<< call conFn [(mem, []), (tag,[]), (voidPtr,[])]
        in do 
           let mkDestrName (Name n) = "~" <> n
               destrName = Name $ mkDestrName conFnName
           conFn <- function conFnName params retType fnBody
           destr <- function destrName [(retType, ParameterName "toFree")] VoidType $ \[toFree] -> do
                       toFreei8 <- bitcast toFree $ PointerType (IntegerType 8) (AddrSpace 0)
                       free <- gets ((\(Just (ContFn m))->m) . (Map.!? "free") . bindMap)
                       call free [(toFreei8, [])]
                       retVoid
           let df = DataFns sz conFn [] Nothing
           modify (\x->x { dataFnsMap = Map.insert name df (dataFnsMap x) })
           return conFn
  genCon memberParams

-- Sum types ~= {i32, i8*}
genSumConstructor :: CodeGenModuleConstraints m
  => StgSumType -> m Operand

-- Only one alt = this sum type is actually a product type
genSumConstructor (StgSumType name [productType]) = genProductConstructor productType Nothing

genSumConstructor algData@(StgSumType name productTypes) = do
  -- Start with a typedef sumtype = {i32, i8*} (tag and pointer)
  let membTypes = [IntegerType 32, charPtrType]
      structName = name ; conFnName = name
      structType = StructureType packed membTypes where packed = False
      sz = sizeof structType
  structType <- typedef structName (Just structType)
  let structPtrType = PointerType structType (AddrSpace 0)
  modify (\x->x { typeMap = Map.insert name (StgLlvmType structPtrType) (typeMap x) })

  -- generate llvm constructor function: `MyType *MyType(i8* mem, i32 tag, i8* union)`
  let params = (charPtrType, ParameterName "Mem") : membParams
        where membParams = zip membTypes (ParameterName <$> ["tag", "unionPtr"])
  conFn <- function conFnName params structPtrType $ \[mem, tag, valVoidPtr] -> do
      sumTyPtr <- bitcast mem structPtrType `named` "return-mem"
      tagPtr <- gep sumTyPtr [constZero, constZero]
      store tagPtr 0 tag
      unionValPtr <- gep sumTyPtr [constZero, ConstantOperand $ C.Int 32 1]
      store unionValPtr 0 valVoidPtr
      ret sumTyPtr -- return this no matter what.

  let datafns = DataFns sz conFn productNames Nothing
        where productNames = (\(StgProductType nm _) -> nm) <$> productTypes
  modify (\x->x { dataFnsMap = Map.insert name datafns (dataFnsMap x) })

  -- generate constructors for all alts
  let mkSubType (StgProductType deConId structTy) tag = do
        conInfo <- gets (aliasToType deConId . typeMap)
        case conInfo of
          Just ty -> error ("Duplicate constructor Name: " ++ show conInfo)
          Nothing -> let pTy = StgProductType deConId structTy
                         tag' = ConstantOperand $ C.Int 32 $ fromInteger tag
                     in genProductConstructor pTy $ Just (InSumType conFn tag' structType)
  zipWithM_ mkSubType productTypes [0..] -- codegen all this sumtypes constructors
  return conFn

-- Get a list of operands from a product type (llvm struct)
-- This just means a few geps
deconProduct :: CodeGenIRConstraints m
  => LLVM.AST.Operand -> (StgId, [StgId], StgExpr) -> m [StgBinding]
deconProduct dataStruct (iden, members, expr) =
  let nMembers = fromIntegral $ length members
      gepArg idx = ConstantOperand . C.Int 32 <$> [0, idx]
      idxToVal idx = gep dataStruct (gepArg idx) >>= \ptr -> load ptr 0

      mkBinding name ssa = StgBinding name (StgRhsSsa ssa)
  in zipWith mkBinding members <$> mapM idxToVal [0 .. nMembers-1]

-- produce a StgCaseSwitch from a dataCase on a sumtype
deconSum :: CodeGenIRConstraints m
  => LLVM.AST.Operand -> Maybe StgExpr -> [(StgId, [StgId], StgExpr)] -> m StgExpr
deconSum dataStruct maybeDefault alts = do
  let [zero,one] = ConstantOperand . C.Int 32 <$> [0, 1]
  tag <- gep dataStruct [zero, zero] >>= \ptr -> load ptr 0 `named` "tag"
  valPtr <- gep dataStruct [zero, one] `named` "valPtr"
  let mkProduct tagNumber subProductType@(iden, fieldNames, expr) =
        gets (aliasToType iden . typeMap) >>= \case
          Nothing -> error ("no deconstructor: " ++ show iden)
          Just (StgTyperef ty subTy) -> do
              let valPtrType = PointerType subTy (AddrSpace 0)
              castStruct <- bitcast valPtr valPtrType `named` "cast"
              val <- load castStruct 0
              -- let tagNumber = getTag iden
              return (C.Int 32 $ fromIntegral tagNumber,
                     -- bitcast to data # tagNumber !
                      StgCase (StgLit (StgSsaArg val))
                              (Just expr)
                              (StgDeconAlts [subProductType])
                      )
          _ -> error "Panic: No subtype" -- ?!
  taggedProducts <- zipWithM mkProduct [(0::Int)..] alts
  pure $ StgCase (StgLit $ StgSsaArg tag) maybeDefault (StgSwitch taggedProducts)
