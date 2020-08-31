{-# Language TypeFamilies #-}
module CodeGen

where

import Prim
import Externs
import CoreSyn
import PrettyCore
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import Control.Monad.ST.Lazy
import Control.Monad.State.Lazy
import Control.Monad.Primitive (PrimMonad,PrimState,primitive)
import Data.Functor
import Data.Function
import Data.Foldable
import qualified Data.Text as T
import qualified Data.IntMap as IM
import qualified Data.Map as M
import qualified Data.IntSet as IS
import Data.List
import Data.Char
import qualified LLVM.AST as L
import qualified LLVM.AST
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.IntegerPredicate as IP
import qualified LLVM.AST.FloatingPointPredicate as FP
import qualified LLVM.AST.FunctionAttribute as FA
import qualified LLVM.AST.Type  as LT
import qualified LLVM.AST.Typed as LT
import qualified LLVM.AST.Float as LF
import           LLVM.AST.AddrSpace
import           LLVM.AST.Global
import LLVM.IRBuilder.Module hiding (function)
import LLVM.IRBuilder.Monad
import LLVM.IRBuilder.Instruction hiding (gep)

import Debug.Trace
panic why = error $ "Panic: Codegen: " ++ why

-- patch up missing PrimMonad instance for lazy ST
instance PrimMonad (ST s) where
  type PrimState (ST s) = s
  primitive = strictToLazyST . primitive

type CGEnv s a = StateT (CGState s) (ST s) a
type CGBodyEnv s a = IRBuilderT (StateT (CGState s) (ST s)) a
--type CGBodyEnv s a = (MonadIRBuilder m , MonadState (CGState s) m, MonadST s m, MonadFix m) => m a

data CGState s = CGState {
   wipBinds   :: MV.MVector s StgWIP
 , externs    :: V.Vector Expr
 , llvmDefs   :: [L.Definition] -- output module contents
 , freshTop   :: Int -- fresh name supply for anonymous module-level defs
 , freshSplit :: Int

 -- meta - stack frame info
 , envArgs       :: [IM.IntMap L.Operand] -- args on stack frame
 , tailSplitTree :: Maybe L.Operand
}

getFreshSplit :: CGEnv s Int
getFreshSplit = gets freshSplit >>= \n -> modify (\x->x{freshSplit = n+1}) $> n+1

data StgWIP
 = TWIP   (HName , Bind)
 | LLVMOp L.Operand         -- normal functions (and global constants)
 | ConstExpr L.Operand
 | LLVMTy L.Type
 | LLVMInstr PrimInstr -- we avoid generating wrappers for these if possible
 deriving Show

mkStg :: V.Vector Expr -> V.Vector (HName , Bind) -> LLVM.AST.Module
mkStg extBinds coreBinds = let
  nBinds = V.length coreBinds
  moduleDefs = runST $ do
    v <- V.thaw (TWIP <$> coreBinds)
    fns' <- MV.new (MV.length v)
    llvmDefs <$> execStateT (cgBind `mapM` [0 .. nBinds-1]) CGState {
        wipBinds = v
      , externs  = extBinds
      , llvmDefs = []
      , freshTop = 0
      , freshSplit = 0

      , envArgs  = []
      , tailSplitTree = Nothing
     }
  in LLVM.AST.defaultModule {
      LLVM.AST.moduleName = ""
    , LLVM.AST.moduleDefinitions = reverse $ moduleDefs
--  , LLVM.AST.moduleTargetTriple = Just "x86_64-pc-linux-gnu"
    }

-- Bindings vary from functions to types to constants to constexprs to instructions
cgBind :: IName -> CGEnv s StgWIP
cgBind i = gets wipBinds >>= \wip -> MV.read wip i >>= \case
 TWIP (nm , bind) -> let
   llvmNm = LLVM.AST.mkName (T.unpack nm)
   in mdo -- handle recursive refs using MonadFix
     MV.write wip i b
     b <- case bind of
       BindOK tt -> case tt of
         Core t ty -> case t of
             Instr instr -> LLVMOp <$> function (L.mkName $ "instr") [intType , intType] intType
               (\[a , b] -> ret =<< emitInstr (LT.typeOf a) ((primInstr2llvm instr) a b))
             m@Match{} -> let
               [THArrow [scrutTy] retTy] = ty
               in cgFunction llvmNm  [(-1 , scrutTy)] [] (m `App` [Var $ VArg (-1)]) retTy []
             x -> cgFunction llvmNm [] [] t ty []
--           x -> panic $ "global constant: " ++ show x
         CoreFn args free t ty -> cgFunction llvmNm args [] t ty []
         Ty ty -> do
           t <- cgType ty
--         emitDef $ L.TypeDefinition llvmNm (Just t)
           pure $ LLVMTy t
       ko -> error "panic Core failed to generate a valid binding"
     pure b
 x -> pure x

lookupArg i = gets ((IM.!? i) . head . envArgs) >>= \case
  Just arg -> pure arg -- local argument
  Nothing  -> gets envArgs >>= \e -> panic $ "arg not in scope: " ++ show i ++ show e

cgTerm :: Term -> CGBodyEnv s L.Operand
cgTerm = let
  cgName = \case
    VBind i -> cgBind i <&> \x -> case x of { LLVMOp x -> x  }
    VArg  i -> lookupArg i
    VExt  i -> _
  in \case
  Var vNm -> lift $ cgName vNm
  Lit l   -> pure . L.ConstantOperand $ literal2Stg l
  Instr i -> _ -- cgPrimInstr i -- Make top-level wrapper for instr
  f `App` args -> case f of
    Instr i -> call (cgPrimInstr i) =<< (map (,[]) <$> cgTerm `mapM` args)
    Match ls d -> case args of
      [x] -> mkSplitTree ((\[x]->x) args) ls d
      _   -> panic $ "Match must have 1 argument"
    f       -> do
      f' <- cgTerm f
      call f' =<< (map (,[]) <$> cgTerm `mapM` args)
  MultiIf ((ifE,thenE):alts) elseE -> let -- convert to tree of switch-cases
    tail = case alts of
      [] -> elseE
      branches -> MultiIf branches elseE
    in genSwitch ifE [(C.Int 1 1 , thenE)] (Just tail)

  Cons fields      -> _
  Proj  t f        -> cgTerm t >>= \t -> loadIdx t f
  Label i args     -> mkLabel (fromIntegral i) ((\(Core t ty)->t) <$> args)
  Match labels d   -> error $ "floating match" -- mkSplitTree Nothing labels d
  List  args       -> _
  x -> error $ "MkStg: not ready for term: " ++ show x

cgType :: [TyHead] -> CGEnv s L.Type
cgType = \case
  [t] -> cgTypeAtomic t
  [THVar{} , THArg{}] -> pure charPtrType
  [THArg{} , THArg{}] -> pure charPtrType
  [] -> pure charPtrType
  x   -> panic $ "lattice Type: " ++ show x

cgTypeAtomic = \case
  THVar b   -> pure $ charPtrType
  THArg i   -> pure $ charPtrType
  THPrim p      -> pure $ primTy2llvm p
  THArrow tys t -> (\ars retTy -> L.FunctionType retTy ars False)
    <$> (cgType `mapM` tys) <*> cgType t
  THArray t     -> _ -- LLVM.AST.ArrayType $ cgType t
  THExt i       -> pure $ intType
  THSum   ls    -> pure $ charPtrType -- TODO
  THSplit ls    -> pure $ charPtrType -- TODO
  THProd p      -> pure $ charPtrType
  x -> error $ "MkStg: not ready for ty: " ++ show x

cgPrimInstr i = case i of
  ExprHole -> _
  MkNum    -> _
  MkReal   -> _
  MkTuple  -> _
  Alloc    -> _
  Len      -> _
  SizeOf   -> _ -- C.sizeof

genSwitch scrutTerm branches defaultBranch = let
  callErrorFn str = _ -- call (errFn str) [] <* unreachable
  genAlt endBlock (scrutVal , expr) = do -- collect (result,block) pairs for the phi instr
    flip (,) <$> block <*> (cgTerm expr <* br endBlock)
  in mdo
  scrut <- cgTerm scrutTerm
  retBlockPairs <- genAlt endBlock `mapM` branches
  switch scrut dBlock (zip (fst <$> branches) (snd <$> retBlockPairs))
  endBlock <- block
  dBlock <- block
  dSsa   <- case defaultBranch of
    Just d  -> cgTerm d *> br endBlock *> phi retBlockPairs
    Nothing -> callErrorFn "NoPatternMatch"
  phi $ (dSsa, dBlock) : retBlockPairs

----------------
-- Primitives --
----------------
literal2Stg :: Literal -> C.Constant = \l ->
  let mkChar c = C.Int 8 $ toInteger $ ord c 
  in case l of
    Char c    -> mkChar c
    String s  -> C.Array (LLVM.AST.IntegerType 8) (mkChar<$>(s++['\0']))
    Array  x  -> C.Array (LLVM.AST.IntegerType 32) (literal2Stg <$> x)
    Int i     -> C.Int 32 $ i
--    Frac f    -> C.Float (LF.Double $ fromRational f)
    x -> error $ show x

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

primTy2llvm :: PrimType -> LLVM.AST.Type =
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

-------------------
-- ModuleBuilder --
-------------------

--emitArray = let
-- zz = [C.Int 32 0, C.Int 32 0]
-- in do
-- emitDef $ GlobalDefinition globalVariableDefaults
--    { name                  = nm
--    , LLVM.AST.Global.type' = ty
--    , linkage               = Private
--    , isConstant            = True
--    , initializer           = Just arr
--    , unnamedAddr           = Just GlobalAddr
--    }
-- pure $ C.GetElementPtr True (C.GlobalReference (ptr ty) nm) zz

cgFunction :: L.Name -> [(IName, [TyHead])] -> [(IName , LT.Type)]
  -> Term -> [TyHead] -> [FA.FunctionAttribute]
  -> CGEnv s StgWIP
cgFunction llvmNm args free t ty attribs = let
  iArgs = (fst<$>args) ++ (fst<$>free)
  in do
  retTy <- cgType ty
  mainArgTys <- (cgType . snd) `mapM` args
  let argTys = mainArgTys ++ (snd<$>free)
  (params , blocks) <- runIRBuilderT emptyIRBuilder $ do
    localArgOps <- argTys `forM` \ty -> L.LocalReference ty <$> fresh
    freeArgOps  <- (snd<$>free) `forM` \ty -> L.LocalReference ty <$> freshName "free"
    let argOps = localArgOps ++ freeArgOps
    modify $ \x -> x { envArgs = IM.fromList (zip iArgs argOps) : envArgs x }
    ret =<< cgTerm t
    modify $ \x -> x { envArgs = drop 1 (envArgs x) }
    pure argOps

  let fnParams = (\(L.LocalReference ty nm) -> Parameter ty nm []) <$> params
      fnDef = L.GlobalDefinition L.functionDefaults
        { name        = llvmNm
        , parameters  = (fnParams , False)
        , returnType  = retTy
        , basicBlocks = blocks
        , functionAttributes = Right <$> attribs
        }
      funty = LT.ptr $ LT.FunctionType retTy argTys False
      fnOp  = L.ConstantOperand $ C.GlobalReference funty llvmNm
  emitDef fnDef
  pure $ LLVMOp fnOp

function :: L.Name -> [LT.Type] -> LT.Type -> ([L.Operand] -> CGBodyEnv s ())
  -> CGEnv s L.Operand
function label argtys retty body = do
  (params, blocks) <- runIRBuilderT emptyIRBuilder $ do
    params <- argtys `forM` \ty -> L.LocalReference ty <$> fresh
    params <$ body params
  let fnParams = (\(L.LocalReference ty nm) -> Parameter ty nm []) <$> params
      def = L.GlobalDefinition L.functionDefaults
        { name        = label
        , parameters  = (fnParams, False)
        , returnType  = retty
        , basicBlocks = blocks
        }
      funty = LT.ptr $ LT.FunctionType retty argtys False
  emitDef def
  pure $ L.ConstantOperand $ C.GlobalReference funty label

emitDef d = modify $ \x->x{llvmDefs = d : llvmDefs x}

--------------------------
-- IRBuilder extensions --
--------------------------
voidPtrType = charPtrType -- llvm doesn't allow void pointers
ptrListType = LT.PointerType (charPtrType) (AddrSpace 0)
charPtrType :: L.Type = LT.PointerType (LT.IntegerType 8) (AddrSpace 0)
intType = LT.IntegerType 32
constI32 = L.ConstantOperand . C.Int 32

load' ptr = load ptr 0
store' ptr op = store ptr 0 op
alloca' ptr op = alloca ptr op 0

gep addr is = let
  ty = gepType (LT.typeOf addr) is
  gepType ty [] = LT.ptr ty
  gepType (LT.PointerType ty _) (_:is') = gepType ty is'
  gepType (LT.StructureType _ elTys) ix = case ix of
    L.ConstantOperand (C.Int 32 val):is' -> gepType (elTys !! fromIntegral val) is'
    x -> error "gep index: expected constI32"
  gepType (LT.VectorType _ elTy) (_:is') = gepType elTy is'
  gepType (LT.ArrayType _ elTy) (_:is') = gepType elTy is'
  gepType x _ = error $ "gep into non-indexable type: " ++ show x
  in emitInstr ty (L.GetElementPtr False addr is [])

-- load a value from an array (~pointer to array)
loadIdx :: L.Operand -> Int -> CGBodyEnv s L.Operand
loadIdx ptr i = let
  gepIdxs = [constI32 0, constI32 $ fromIntegral i]
  in ptr `gep` gepIdxs >>= load'
storeIdx ptr i op = let
  gepIdxs = [constI32 0, constI32 $ fromIntegral i]
  in ptr `gep` gepIdxs >>= (`store'` op)

-- make a list of pointers on the stack
mkPtrList ops = do
  ptr <- alloca' voidPtrType (Just $ constI32 (fromIntegral $ length ops))
  let writeIdx idx op = do
        p <- ptr `gep` [constI32 $ fromIntegral idx]
        store' p =<< bitcast op charPtrType
  ptr <$ zipWithM_ writeIdx [0..] ops
mkSizedPtrList ops = let -- + size variable
  sz = constI32 (fromIntegral $ 1 + length ops) -- C.Int 32 (fromIntegral $ 1 + length ops)
  in do
  ptr <- alloca' voidPtrType (Just sz)
  storeIdx ptr 0 sz
  ptr <$ zipWithM (storeIdx ptr) [1..] ops

mkTagged tag val = do
  ptr <- alloca' (LT.StructureType False [intType , LT.typeOf val]) Nothing
  ptr <$ do
    storeIdx ptr 0 tag
    storeIdx ptr 1 val

mkStruct vals = do
  ptr <- alloca' (LT.StructureType False (LT.typeOf <$> vals)) Nothing
  ptr <$ zipWithM (storeIdx ptr) [0..] vals

pApAp pap papArity llArgs =
  (loadIdx pap `mapM` [0..1+papArity]) >>= \case
    fn : papArgs -> call fn $ (,[]) <$> papArgs ++ llArgs

----------
-- Data --
----------
tagFnPtr : tagPAp : tagRec : tagSplitTree : _ = constI32 <$> [0..]

mkLabel label tts = mkStruct . (constI32 label :) =<< (cgTerm `mapM` tts)

-- tail call upstack splitTree
tailSplit tailST label = _

-- # SplitTree = { [freeVars] ; [ || fnPtr | PAp | rec | SplitTree || ] }
mkSplitTree label labelMap _defaultFn = let
  getFn = \case { LLVMOp x -> x }
  mkAlt (CoreFn ars free term ty) = do
    nm <- L.mkName . ("splitFn"++) . show <$> lift getFreshSplit
    freeVars <- (\i -> (i,) . LT.typeOf <$> lookupArg i) `mapM` IS.toList free
    getFn <$> lift (cgFunction nm ars freeVars term ty [])
  mkAlt (Core term _ty) = do
    e <- cgTerm term
    pure e
--  mkTagged tagFnPtr e
  in do
  st <- mkStruct =<< (mkAlt `mapM` (IM.elems labelMap))
  case label of
    f `App` x -> _
    l         -> evalSplitTree st =<< cgTerm label

evalSplitTree st l = do
  tag <- load' =<< (l `gep` [constI32 0])
  alt <- load' =<< (st `gep` [tag , constI32 0])
  pure alt
  call alt [(l,[])]

splitEager label match = _
