{-# Language TypeFamilies #-}
module Prim2LLVM where

import Prim
import CoreSyn
import PrettyCore
import Control.Monad.ST.Lazy
import Control.Monad.State.Lazy
import Control.Monad.Primitive (PrimMonad,PrimState,primitive)
import Data.Functor
import Data.Function
import Data.Maybe
import Data.String
import qualified Data.ByteString.Short as BS
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.IntMap as IM
import qualified Data.Map as M
import qualified LLVM.AST as L
import qualified LLVM.AST.Type as LT
import qualified LLVM.AST.Typed as LT
import qualified LLVM.AST.IntegerPredicate as IP
import qualified LLVM.AST.FloatingPointPredicate as FP
import qualified LLVM.AST.Constant as C
import LLVM.AST.AddrSpace
import LLVM.AST.Global
import LLVM.AST.Linkage
import LLVM.IRBuilder.Module hiding (function)
import LLVM.IRBuilder.Monad
import LLVM.IRBuilder.Instruction hiding (gep)

panic why = error $ "Panic: Codegen: " ++ why

-- patch up missing PrimMonad instance for lazy ST
instance PrimMonad (ST s) where
  type PrimState (ST s) = s
  primitive = strictToLazyST . primitive

type CGEnv s a = StateT (CGState s) (ST s) a
type CGBodyEnv s a = IRBuilderT (StateT (CGState s) (ST s)) a

data CGState s = CGState {
   wipBinds   :: MV.MVector s StgWIP
 , externs    :: V.Vector Expr
 , llvmDefs   :: [L.Definition] -- output module contents

 , moduleUsedNames :: M.Map BS.ShortByteString Int

 -- meta - stack frame info
 , envArgs   :: [IM.IntMap L.Operand] -- args on stack frame
}

freshTopName :: BS.ShortByteString -> CGEnv s L.Name
freshTopName suggestion = do
  nameCount <- gets (fromMaybe 0 . (M.!? suggestion) . moduleUsedNames)
  modify $ \x->x{ moduleUsedNames = M.insert suggestion (nameCount + 1) (moduleUsedNames x) }
  pure $ L.Name $ "." <> suggestion <> "." <> fromString (show nameCount)

data StgWIP
 = TWIP   (HName , Bind)
 | LLVMFn { freeArgs :: [IName] , fnOp :: L.Operand }
 | LLVMTy L.Type
 | LLVMInstr PrimInstr -- we avoid generating wrappers for these if possible
 deriving Show

-- most llvm instructions take flags, stg wants functions on operands
primInstr2llvm :: PrimInstr -> (L.Operand -> L.Operand -> L.Instruction) = \case
  IntInstr i  -> case i of
      Add  -> \a b -> L.Add False False a b []
      Sub  -> \a b -> L.Sub False False a b []
      Mul  -> \a b -> L.Mul False False a b []
      SDiv -> \a b -> L.SDiv False      a b []
      SRem -> \a b -> L.SRem            a b []
      ICmp -> \a b -> L.ICmp IP.EQ      a b []
      And  -> \a b -> L.And             a b []
      Or   -> \a b -> L.Or              a b []
      Xor  -> \a b -> L.Xor             a b []
      Shl  -> \a b -> L.Shl False False a b []
      Shr  -> \a b -> L.LShr False      a b []
  NatInstr i  -> case i of
      UDiv -> \a b -> L.UDiv False a b []
      URem -> \a b -> L.URem a b []
  FracInstr i -> case i of
      FAdd -> \a b -> L.FAdd L.noFastMathFlags a b []
      FSub -> \a b -> L.FSub L.noFastMathFlags a b []
      FMul -> \a b -> L.FMul L.noFastMathFlags a b []
      FDiv -> \a b -> L.FDiv L.noFastMathFlags a b []
      FRem -> \a b -> L.FRem L.noFastMathFlags a b []
      FCmp -> \a b -> L.FCmp FP.UEQ a b []
  t -> error $ show t

primTy2llvm :: PrimType -> L.Type =
  let doExtern isVa tys =
        let (argTys, [retTy]) = splitAt (length tys -1) tys
        in LT.FunctionType retTy argTys isVa
  in \case
  PrimInt   i   -> LT.IntegerType $ fromIntegral i
  PrimFloat f   -> LT.FloatingPointType $ case f of
      HalfTy    -> LT.HalfFP
      FloatTy   -> LT.FloatFP
      DoubleTy  -> LT.DoubleFP
      FP128     -> LT.FP128FP
      PPC_FP128 -> LT.PPC_FP128FP
  PtrTo ty      -> LT.PointerType (primTy2llvm ty) (AddrSpace 0)
  PrimExtern   argTys -> doExtern False (primTy2llvm <$> argTys)
  PrimExternVA argTys -> doExtern True  (primTy2llvm <$> argTys)
  PrimArr t     -> _
  PrimTuple tys -> -- StgTuple (primTy2llvm <$> tys)
    let structTy = LT.StructureType False (primTy2llvm <$> tys)
    in  LT.PointerType structTy (AddrSpace 0)

-- Module Builder
emitDef d = modify $ \x->x{llvmDefs = d : llvmDefs x}

emitArray :: L.Name -> [C.Constant] -> CGEnv s C.Constant
emitArray nm arr = let
 elemTy = LT.typeOf (head arr)
 llvmArr = C.Array elemTy arr
 ty = LT.typeOf llvmArr
 in C.GetElementPtr True (C.GlobalReference (LT.ptr ty) nm) [C.Int 32 0, C.Int 32 0]
 <$ (emitDef . L.GlobalDefinition) globalVariableDefaults
    { name        = nm
    , type'       = ty
    , linkage     = Private
    , isConstant  = True
    , initializer = Just llvmArr
    , unnamedAddr = Just GlobalAddr
    }

--------------------------
-- IRBuilder extensions --
--------------------------
--voidPtrType = charPtrType -- llvm doesn't allow void pointers
voidPtrType = LT.ptr $ LT.NamedTypeReference "ANY"
polyType = LT.ptr $ LT.NamedTypeReference "A"
charPtrType :: L.Type = LT.PointerType (LT.IntegerType 8) (AddrSpace 0)
intType    = LT.IntegerType 32
boolType   = LT.IntegerType 1
constI32   = L.ConstantOperand . C.Int 32
polyFnType'= LT.FunctionType voidPtrType [] True -- `char* f(..)`
polyFnType = LT.ptr polyFnType'
varArgsFnTy retTy = LT.ptr $ LT.FunctionType retTy [] True

load' ptr = load ptr 0
store' ptr op = store ptr 0 op
alloca' ty op = alloca ty op 0
call' f = call f . map (,[])
mkNullPtr = L.ConstantOperand . C.Null

gep :: L.Operand -> [L.Operand] -> CGBodyEnv s L.Operand
gep addr is = let
  ty = gepType (LT.typeOf addr) is
  gepType ty [] = LT.ptr ty
  gepType (LT.PointerType ty _) (_:is') = gepType ty is'
  gepType (LT.StructureType _ elTys) ix = case ix of
    L.ConstantOperand (C.Int 32 val):is' -> if length elTys <= (fromIntegral val) then panic $ "gep: " ++ show val ++ show elTys else gepType (elTys !! fromIntegral val) is'
    x -> error "gep index: expected constI32"
  gepType (LT.VectorType _ elTy) (_:is') = gepType elTy is'
  gepType (LT.ArrayType _ elTy) (_:is') = gepType elTy is'
  gepType (LT.NamedTypeReference nm) is
    | nm == typeDefLabel = gepType tyLabel' is
    | nm == typeDefAltMap = gepType tyAltMap' is
    | nm == typeDefSplitTree = gepType tySplitTree' is
    | nm == typeDefSTCont = gepType tySTCont' is
    | nm == typeDefSTAlts = gepType tySTAlts' is

    | otherwise = panic $ "unknown typedef: " ++ show nm
  gepType x _ = error $ "gep into non-indexable type: " ++ show x
  in emitInstr ty $ (L.GetElementPtr False addr is [])

-- load a value from an array (~pointer to array)
loadIdx :: L.Operand -> Int -> CGBodyEnv s L.Operand
loadIdx ptr i = load' =<< (ptr `gep` [constI32 0, constI32 $ fromIntegral i])
storeIdx :: L.Operand -> Int -> L.Operand -> CGBodyEnv s ()
storeIdx ptr i op = (`store'` op) =<< ptr `gep` [constI32 0, constI32 $ fromIntegral i]

-- make a list of pointers on the stack
mkPtrList :: LT.Type -> [L.Operand] -> CGBodyEnv s L.Operand
mkPtrList ty ops = do
  let len = length ops
      arrTy = LT.ArrayType (fromIntegral len) ty
      undef = L.ConstantOperand (C.Undef arrTy)
  ptr <- alloca' arrTy Nothing `named` "ptrList"
  arr <- foldM (\arr (i,val) -> insertValue arr val [i]) undef (zip [0..] ops)
  store' ptr arr
  pure ptr

mkSizedPtrList ops = flip named "ptrListSZ" $  let -- + size variable
  ptrType = voidPtrType
  sz = fromIntegral $ length ops -- C.Int 32 (fromIntegral $ 1 + length ops)
  structType = LT.StructureType False [ intType , LT.ArrayType sz ptrType ]
  in do
  ptr <- alloca' structType Nothing
  storeIdx ptr 0 (constI32 $ fromIntegral sz)
  ptrList <- ptr `gep` [constI32 1]
  ptr <$ zipWithM (storeIdx ptrList) [0..] ops

mkStruct :: Maybe L.Type -> [L.Operand] -> CGBodyEnv s L.Operand
mkStruct maybeTy vals = let
  ty    = case maybeTy of
    Nothing -> LT.StructureType False (LT.typeOf <$> vals)
    Just ty -> ty
  undef = L.ConstantOperand (C.Undef ty)
  in do
    ptr <- alloca' ty Nothing
    struct <- foldM (\struct (i,val) -> insertValue struct val [i]) undef (zip [0..] vals)
    ptr <$ store' ptr struct

pApAp pap papArity llArgs =
  (loadIdx pap `mapM` [0..1+papArity]) >>= \case
    fn : papArgs -> call fn $ (,[]) <$> papArgs ++ llArgs

mkBranchTable :: Bool -> L.Operand -> [(BS.ShortByteString , CGBodyEnv s L.Operand)] -> CGBodyEnv s L.Operand
mkBranchTable doPhi scrut alts = mdo
  switch scrut defaultBlock (zip (C.Int 32 <$> [0..]) entryBlocks)
  (entryBlocks , phiNodes) <- unzip <$> alts `forM` \(blockNm , cg) -> do
    b <- block `named` blockNm
    code <- cg <* br endBlock
    endBlock <- currentBlock
    pure (b , (code , endBlock))
  defaultBlock <- (block `named` "default") <* unreachable
  endBlock <- block `named` "end"
  if doPhi then phi phiNodes
  else pure (L.ConstantOperand C.TokenNone)

----------
-- Data --
----------
-- Crucially, functions may never return labels in llvm, so:
-- Splitters (Label -> Value) become (Label -> st -> Value)
-- Conts     (Label -> Label) become (Label -> st -> Value)
-- Gen       (Value -> Label) become (Value -> st -> Value) 'takes tailTree'
--
-- alts = [ || fnPtr | PAp | rec | SplitTree || ]
-- cont = { fn } -- fn will compute a splitTree
-- none = {}
-- record = [ ptr ]
-- SplitTree = || none | cont | alts | record ||

-- typedefs
structTypeDef nm tys = (nm , LT.StructureType False tys, LT.ptr (LT.NamedTypeReference nm))

dataFnType = LT.ptr $ LT.FunctionType LT.VoidType [voidPtrType , tySplitTree] True -- `char* f(..)`
(typeDefLabel  , tyLabel' , tyLabel) = structTypeDef "label" [intType , voidPtrType]
(typeDefSplitTree , tySplitTree' , tySplitTree) = structTypeDef "splitTree" [tySplitTree , intType]
(typeDefSTCont , tySTCont' , tySTCont) = structTypeDef "STCont" [tySplitTree , intType , dataFnType]
(typeDefSTAlts , tySTAlts' , tySTAlts) = structTypeDef "STAlts" [tySplitTree , intType , LT.ptr tyAltMap]
(typeDefAltMap , tyAltMap' , tyAltMap) = structTypeDef "alt"   [intType , dataFnType , voidPtrType]


tagsSTAlt = C.Int 32 <$> [0..]
tagAltFn : tagAltPAp : tagAltRec : tagAltRecPAp : _ = L.ConstantOperand <$> tagsSTAlt

tagsSplitTree = C.Int 32 <$> [0..]
tagSTAlts : tagSTCont : tagSTRecord : _ = L.ConstantOperand <$> tagsSplitTree

