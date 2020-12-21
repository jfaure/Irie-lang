{-# Language TypeFamilies #-}
module Prim2LLVM where

import Prim
import CoreSyn
import Externs
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
import qualified Data.IntSet as IS
import qualified Data.Map as M
--import qualified Data.HashMap as H
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

-- nat, nat, array, irregular array, tree
-- TODO wrapper types ? esp. optimize extracting data out of a container
data DataTypes = Enum | Peano | Flat | SumTypeList | Tree
data SubData = SubData | Wrap

-- patch up missing PrimMonad instance for lazy ST
instance PrimMonad (ST s) where
  type PrimState (ST s) = s
  primitive = strictToLazyST . primitive

type CGEnv s a = StateT (CGState s) (ST s) a
type CGBodyEnv s a = IRBuilderT (StateT (CGState s) (ST s)) a
data CGState s = CGState {
 -- Input
   wipBinds   :: MV.MVector s StgWIP
 , externs    :: Externs --V.Vector Expr
 , coreModule :: JudgedModule

 -- Output
 , llvmDefs   :: [L.Definition]

 -- Internal State
 , moduleUsedNames :: M.Map BS.ShortByteString Int
 , stack           :: [CallGraph s]
}

data CallGraph s = CallGraph {
   regArgs      :: IM.IntMap L.Operand
 , dataArgs     :: IM.IntMap DataArg -- incl. temp datas. these must all be consumed !
 , splits       :: [Split]   -- sumtypes split earlier on this SF
} deriving Show

data DataArg = DataArg { qtt :: Int , aframe :: L.Operand , dOp :: L.Operand } deriving Show

data Split = Split { -- a data opened by Match (may be reused or freed)
   lname      :: ILabel
 , sframe     :: L.Operand -- the parent frame
 , components :: IM.IntMap L.Operand -- datas here were split from this SF
} deriving Show

-- currency used in the code generator
data STGOp = STGOp  {
   op  :: L.Operand
 , fr  :: Maybe DataFrame
} deriving Show
type DataFrame = L.Operand
--data DataFrame = TreeFrame L.Operand | FlatFrame L.Operand
--data DataFrame = DFTree { getDFrame :: L.Operand } | DFList { getDFrame :: L.Operand } deriving Show

-- TODO
-- * trim (fn property)
-- * dups
-- Want to know: qtt of arg use + arg build

-- ??
-- inplaceing sublists
-- Implicit pointers (esp. flat data)
-- paps (pap vs fn ptr)
-- poly & copyable data
-- wrap frames; eg. containers (to avoid frame-merge)
-- size classes + extensible fastbins (on frame-merge)
-- foldr elim ; foldr f z = \case Empty => z ; (Leaf x) => f x z ; (Node l k r) => foldr f (f k (foldr f z r)) l
-- extraction (esp. list)

-- !!
-- Builder qtt
-- PAP: fn ptrs are lists of ptrs, if first is NULL, then it's a PAP

-- fnDef:
--   dataArgs become 2 args; add the frame
-- fnApp:
--   dup args if needed by fn
--   codegen each arg + give fn frame
--   maybe end the ret frame builder
-- Label: like fnApp, also
--   merge data arg frames (or make a frame)
--   either newFrag, or pushFlat
-- Match:
--   insert extra dups on each branch ; report min for the whole branch statement
--   register split data (basically directly inline the splitter fns)
--   if frame not used: then free frame else free frags (if useful)

modifySF f = modify $ \x->x { stack = (\(x:xs) -> f x : xs) (stack x) }

data StgWIP
 = TWIP   (HName , Bind)

 | STGFn     { retData :: Bool , freeArgs :: [IName] , fnOp :: L.Operand }
-- | STGDataFn { freeArgs :: [IName] , fnOp :: L.Operand , sts :: IM.IntMap QTT }
 | STGConstant { fnOp :: L.Operand } -- top level functions for now

 | LLVMTy L.Type
 | LLVMInstr PrimInstr -- we avoid generating functions for these if possible
 deriving Show

getVAFn retTy nm = L.ConstantOperand (C.GlobalReference (LT.ptr $ LT.FunctionType retTy [] True) (L.mkName nm))
frAlloc_mergeFrames args      = getVAFn frameType   "fralloc_mergeFrames" `call'` args
frAlloc_shareFrame args       = getVAFn frameType   "fralloc_shareFrames" `call'` [args]
frAlloc_freeFrame frame       = getVAFn voidPtrType "fralloc_freeFrame" `call'` [frame]
frAlloc_isSingle frame        = getVAFn intType     "fralloc_isSingle" `call'` [frame]
frAlloc_new frame sz          = getVAFn voidPtrType "fralloc_newFrag" `call'` [frame , sz]
frAlloc_freeFrag frame ptr sz = getVAFn voidPtrType "fralloc_freeFrag" `call'` [frame,ptr,sz]

frAlloc_DFList_mergeFrames args = getVAFn frameType "fralloc_DFList_mergeFrames" `call'` args
frAlloc_push frame sz           = getVAFn voidPtrType "fralloc_push" `call'` [frame , sz]
frAlloc_pop  frame ptr sz       = getVAFn voidPtrType "fralloc_pop" `call'` [frame,sz] -- ! no ptr needed

freshTopName :: BS.ShortByteString -> CGEnv s L.Name
freshTopName suggestion = do
  nameCount <- gets (fromMaybe 0 . (M.!? suggestion) . moduleUsedNames)
  modify $ \x->x{ moduleUsedNames = M.insert suggestion (nameCount + 1) (moduleUsedNames x) }
  pure $ L.Name $ "." <> suggestion <> "." <> fromString (show nameCount)

-- most llvm instructions take flags, stg wants functions on operands
primInstr2llvm :: PrimInstr -> (L.Operand -> L.Operand -> L.Instruction) = \case
  IntInstr i  -> case i of
      Add  -> \a b -> L.Add False False a b []
      Sub  -> \a b -> L.Sub False False a b []
      Mul  -> \a b -> L.Mul False False a b []
      SDiv -> \a b -> L.SDiv False      a b []
      SRem -> \a b -> L.SRem            a b []
      And  -> \a b -> L.And             a b []
      Or   -> \a b -> L.Or              a b []
      Xor  -> \a b -> L.Xor             a b []
      Shl  -> \a b -> L.Shl False False a b []
      Shr  -> \a b -> L.LShr False      a b []
  PredInstr p -> case p of
      EQCmp-> \a b -> L.ICmp IP.EQ      a b []
      LECmp-> \a b -> L.ICmp IP.SLE     a b []
      GECmp-> \a b -> L.ICmp IP.SGE     a b []
      LCmp -> \a b -> L.ICmp IP.SLT     a b []
      GCmp -> \a b -> L.ICmp IP.SGT     a b []
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

-- basically is it bigger than register size
isDataTyHead = \case { THSum{}->True ; THSplit{}->True ; THProd{}->True ; THRec{}->True ; THExt 21->True ; _->False } -- HACK

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
tagBits = 32
voidPtrType = LT.ptr $ LT.NamedTypeReference "ANY"
frameType   = LT.ptr $ LT.NamedTypeReference "Fr"
polyType = voidPtrType -- LT.ptr $ LT.NamedTypeReference "A"
charPtrType :: L.Type = LT.PointerType (LT.IntegerType 8) (AddrSpace 0)
intType    = LT.IntegerType 32
sumTagType = LT.IntegerType tagBits
constTag   = L.ConstantOperand . C.Int tagBits
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
--  | nm == structName label = gepType (rawStructType label) is
    | otherwise = panic $ "unknown typedef: " ++ show nm
  gepType x _ = error $ "gep into non-indexable type: " ++ show x
  in emitInstr ty $ (L.GetElementPtr False addr is [])

-- load a value from an array (~pointer to array)
loadIdx :: L.Operand -> Int -> CGBodyEnv s L.Operand
loadIdx ptr i = load' =<< (ptr `gep` [constI32 0, constI32 $ fromIntegral i])
storeIdx :: L.Operand -> Int -> L.Operand -> CGBodyEnv s ()
storeIdx ptr i op = (`store'` op) =<< ptr `gep` [constI32 0, constI32 $ fromIntegral i]

mkArray ar = let
  ty = LT.typeOf $ head ar
  undef = L.ConstantOperand $ C.Undef $ LT.ArrayType (fromIntegral$length ar) ty
  in foldM (\arr (i,val) -> insertValue arr val [i]) undef (zip [0..] ar)

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

mkSizedPtrList ptrType ops = flip named "ptrListSZ" $  let -- + size variable
  sz = fromIntegral $ length ops -- C.Int 32 (fromIntegral $ 1 + length ops)
  arrTy = LT.ArrayType sz ptrType
  structType = LT.StructureType False [ intType , arrTy ]
  undef = L.ConstantOperand (C.Undef arrTy)
  in do
  ptr <- alloca' structType Nothing
  storeIdx ptr 0 (constI32 $ fromIntegral sz)
  ptrList <- foldM (\arr (i,v) -> insertValue arr v [i]) undef (zip [0..] ops)
  storeIdx ptr 1 ptrList
  pure ptr

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

-- TODO emit lookup tables for very likely case of juxtapposed tags
-- mkBranchTable :: Bool -> L.Operand -> [(BS.ShortByteString , CGBodyEnv s L.Operand)] -> CGBodyEnv s L.Operand
-- mkBranchTable doPhi scrut alts = mdo
--   switch scrut defaultBlock (zip (C.Int 32 <$> [0..]) entryBlocks)
--   (entryBlocks , phiNodes) <- unzip <$> alts `forM` \(blockNm , cg) -> do
--     b <- block `named` blockNm
--     code <- cg <* br endBlock
--     endBlock <- currentBlock
--     pure (b , (code , endBlock))
--   defaultBlock <- (block `named` "default") <* unreachable
--   endBlock <- block `named` "end"
--   if doPhi then phi phiNodes
--   else pure (L.ConstantOperand C.TokenNone)

mkBranchTable :: L.Operand -> [C.Constant] -> [(BS.ShortByteString , CGBodyEnv s STGOp)] -> CGBodyEnv s STGOp
mkBranchTable scrut labels alts = mdo
  switch scrut defaultBlock (zip labels entryBlocks)
  (entryBlocks , phiNodes , phiNodesFrames) <- unzip3 <$> alts `forM` \(blockNm , cg) -> do
    entry <- block `named` blockNm
    STGOp retOp maybeDFrame <- cg <* br endBlock
    exit <- currentBlock
    pure (entry , (retOp , exit) , (,exit) <$> maybeDFrame)
  defaultBlock <- (block `named` "default") <* unreachable
  endBlock <- block `named` "end"
  op <- phi phiNodes
  dframe <- case catMaybes phiNodesFrames of
    []  -> pure Nothing
    ars -> Just <$> phi ars
  pure $ STGOp op dframe
