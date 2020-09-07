module CodeGen (mkStg) where
import Prim
import Prim2LLVM
import Externs
import CoreSyn
import PrettyCore
import Control.Monad.ST.Lazy
import Control.Monad.State.Lazy
import Control.Monad.Primitive (PrimMonad,PrimState,primitive)
import Data.Functor
import Data.Function
import Data.Foldable
import Data.Char
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.Text as T
import qualified Data.IntMap as IM
import qualified Data.Map as M
import qualified Data.IntSet as IS
import qualified Data.ByteString.Short as BS
import qualified LLVM.AST as L
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.IntegerPredicate as IP
import qualified LLVM.AST.FloatingPointPredicate as FP
import qualified LLVM.AST.FunctionAttribute as FA
import qualified LLVM.AST.Type  as LT
import qualified LLVM.AST.Typed as LT
import qualified LLVM.AST.Float as LF
import           LLVM.AST.AddrSpace
import           LLVM.AST.Global
import           LLVM.AST.Linkage as L
import           LLVM.AST.CallingConvention as CC
import LLVM.IRBuilder.Module hiding (function)
import LLVM.IRBuilder.Monad
import LLVM.IRBuilder.Instruction hiding (gep)

import Debug.Trace
mkStg :: V.Vector Expr -> V.Vector (HName , Bind) -> L.Module
mkStg extBinds coreBinds = let
  nBinds = V.length coreBinds
  moduleDefs = runST $ do
    v <- V.thaw (TWIP <$> coreBinds)
    fns' <- MV.new (MV.length v)
    llvmDefs <$> execStateT (mkEvalSplitTreeFn *> (cgBind `mapM` [0 .. nBinds-1])) CGState {
        wipBinds = v
      , externs  = extBinds
      , llvmDefs =
        [ L.TypeDefinition typeDefLabel (Just tyLabel')
        , L.TypeDefinition typeDefAltMap (Just tyAltMap')
        , L.TypeDefinition typeDefSplitTree (Just tySplitTree')
        , L.TypeDefinition typeDefSTCont (Just tySTCont')
        , L.TypeDefinition typeDefSTAlts (Just tySTAlts')
        , L.TypeDefinition "ANY" Nothing
        , L.TypeDefinition "A" Nothing
        , L.GlobalDefinition functionDefaults
          { name=L.mkName "printf"
          , linkage=L.External , parameters=([] , True) , returnType=intType }
        , L.GlobalDefinition functionDefaults
          { name=L.mkName "llvm.uadd.with.overflow.i32"
          , linkage=L.External , parameters=([] , True)
          , returnType=LT.StructureType False [intType , LT.IntegerType 1] }
        ]
      , freshTop   = 0
      , freshSplit = 0
      , freshStr   = 0

      , envArgs  = []
     }
  in L.defaultModule {
      L.moduleName = ""
    , L.moduleDefinitions = reverse $ moduleDefs
--  , T.moduleTargetTriple = Just "x86_64-pc-linux-gnu"
    }

-- Bindings vary from functions to types to constants to constexprs to instructions
cgBind :: IName -> CGEnv s StgWIP
cgBind i = gets wipBinds >>= \wip -> MV.read wip i >>= \case
 TWIP (nm , bind) -> let
   llvmNm = L.mkName (T.unpack nm)
   in mdo -- handle recursive refs using MonadFix
     MV.write wip i b
     b <- case bind of
       BindOK tt -> case tt of
         Core (Instr instr) ty ->
           LLVMFn [] <$> function (L.mkName $ "instr") [intType , intType] intType
             (\[a , b] -> ret =<< emitInstr (LT.typeOf a) ((primInstr2llvm instr) a b))
         Core t ty -> -- panic $ "not ready for constants" ++ show tt
           cgFunction llvmNm [] [] (cgTerm t) ty []
           -- TODO ? use llvm.global_ctors : appending global [ n x { i32, void ()*, i8* } ]
         CoreFn args free t ty -> cgFunction llvmNm args [] (cgTerm t) ty []
         Ty ty -> do
           t <- cgType ty
--         emitDef $ L.TypeDefinition llvmNm (Just t)
           pure $ LLVMTy t
       ko -> error "panic Core failed to generate a valid binding"
     pure b
 x -> pure x

lookupArg i = gets ((IM.!? i) . head . envArgs) >>= \case
  Just arg -> pure arg -- local argument
  Nothing  -> gets envArgs >>= \e -> panic $ "arg not in scope: " ++ show i ++ "\nin: " ++ show (IM.keys <$> e)

cgTerm :: Term -> CGBodyEnv s L.Operand
cgTerm = let
  cgName = \case
    VBind i -> fnOp <$> cgBind i
    VArg  i -> lookupArg i
    VExt  i -> _
  in \case
  Var vNm -> lift $ cgName vNm
  Lit l   -> L.ConstantOperand <$> lift (literal2Stg l)
  Instr i -> error $ show i -- cgPrimInstr i -- Make top-level wrapper for instr
  App f args -> cgApp f args
  MultiIf ((ifE,thenE):alts) elseE ->  -- convert to tree of switch-cases
    genSwitch ifE [(C.Int 1 1 , thenE)] . Just $ case alts of
      [] -> elseE
      branches -> MultiIf branches elseE

  Cons fields      -> _
  Proj  t f        -> cgTerm t >>= \t -> loadIdx t f
  Label i args     -> mkLabel (fromIntegral i) ((\(Core t ty)->t) <$> args)
  Match ty labels d   -> error $ "floating match" -- mkSplitTree Nothing labels d
  List  args       -> _
  x -> error $ "MkStg: not ready for term: " ++ show x

cgApp :: Term -> [Term] -> CGBodyEnv s L.Operand
cgApp f args = case f of
  Instr i    -> cgInstrApp i args
  Match ty ls d -> case args of
    [x] -> lift (cgType ty) >>= \ty' -> mkSplitTree ty' x ls d
    _   -> panic $ "Match must have 1 argument"
  f ->  do
    f1 <- cgTerm f
    case args of
      -- Split-Tree chain
      [id@(Var (VBind 1)) `App` [label]] -> do
        f2 <- cgTerm id
        l  <- cgTerm label
        s1 <- mkSTCont (L.ConstantOperand $ C.Null tySplitTree) f1
        s2 <- mkSTCont s1 f2
        evalSplitTree intType s2 l
      args -> let
        in do
        llArgs <- cgTerm `mapM` args
        if any (isLabelTy . LT.typeOf) llArgs
        then do
          f1' <- bitcast f1 dataFnType
          s1  <- mkSTCont (L.ConstantOperand (C.Null tySplitTree)) f1' `named` "stCont"
          evalSplitTree intType s1 ((\[l] -> l) llArgs)
        else call f1 (map (,[]) llArgs)

isLabelTy x = case x of
  LT.PointerType{} -> case LT.pointerReferent x of
    LT.NamedTypeReference nm -> nm==L.mkName "label"
    _ -> False
  _ -> False

--  if contSplit
--  then do
--    fST <- mkSTCont f'
--    storeIdx args
--    call ar (fST,[])
--  else call f' (map (,[]) args)

--  args <- gets tailSplit >>= \case
--    Nothing : _ -> cgTerm `mapM` args
--    Just st : _ -> (fst st :) <$> cgTerm `mapM` args

cgInstrApp instr args = case instr of
    PutNbr -> call (L.ConstantOperand (C.GlobalReference (LT.ptr $ LT.FunctionType intType [] True) (L.mkName "printf"))) =<< (map (,[]) <$> cgTerm `mapM` (Lit (String "%d\n") : args))
    CallExt nm -> let
      llvmNm = L.mkName (T.unpack nm)
      fn = C.GlobalReference (LT.ptr $ LT.FunctionType intType [] True) llvmNm
      in call (L.ConstantOperand fn) =<<  (map (,[]) <$> cgTerm `mapM` args)
    Zext    -> cgTerm `mapM` args >>= \[a] -> zext a intType
    IfThenE -> (\[ifE, thenE, elseE] -> genSwitch ifE [(C.Int 1 1 , thenE)] (Just elseE)) args
    AddOverflow -> _
    i -> emitInstr intType =<< (\instr [a,b] -> instr a b) (cgPrimInstr i) <$> (cgTerm `mapM` args)

cgType :: [TyHead] -> CGEnv s L.Type
cgType = \case
  [t] -> cgTypeAtomic t
  [THExt 1 , x] -> pure $ intType
  []  -> pure $ intType
  x   -> pure polyType
--x   -> panic $ "lattice Type: " ++ show x

cgTypeAtomic = let
  voidPtrType = polyType -- tyLabel -- LT.ptr $ LT.StructureType False []
  in \case
  THVar{}   -> pure $ voidPtrType
  THArg{}   -> pure $ voidPtrType
  THPrim p      -> pure $ primTy2llvm p
  THArrow tys t -> (\ars retTy -> L.FunctionType retTy ars False)
    <$> (cgType `mapM` tys) <*> cgType t
  THArray t     -> _ -- LT.ArrayType $ cgType t
  THExt 0       -> pure $ boolType
  THExt 1       -> pure $ intType
  THSum   ls    -> pure $ tyLabel
  THSplit ls    -> pure $ tyLabel
  THProd p      -> pure $ voidPtrType
  THRec{}       -> pure $ voidPtrType
  x -> error $ "MkStg: not ready for ty: " ++ show x

cgPrimInstr i = case i of
  ExprHole -> _
  MkNum    -> _
  MkReal   -> _
  MkTuple  -> _
  Alloc    -> _
  Len      -> _
  SizeOf   -> _ -- C.sizeof
  x -> primInstr2llvm i

genSwitch :: Term -> [(C.Constant , Term)] -> Maybe Term -> CGBodyEnv s L.Operand
genSwitch scrutTerm branches defaultBranch = let
  callErrorFn str = _ -- call (errFn str) [] <* unreachable
  genAlt endBlock (scrutVal , expr) = do -- collect (result,block) pairs for the phi instr
    flip (,) <$> block <*> (cgTerm expr <* br endBlock)
  in mdo
  scrut <- cgTerm scrutTerm
  switch scrut dBlock (zip (fst <$> branches) (snd <$> retBlockPairs))
  dBlock   <- (block `named`"switchDefault")
  dSsa   <- case defaultBranch of
    Just d  -> cgTerm d <* br endBlock
    Nothing -> callErrorFn "NoPatternMatch"
  retBlockPairs <- genAlt endBlock `mapM` branches
  endBlock <- block `named` "switchEnd"
  phi $ (dSsa, dBlock) : retBlockPairs

----------------
-- Primitives --
----------------
literal2Stg :: Literal -> CGEnv s C.Constant
literal2Stg l =
  let mkChar c = C.Int 8 $ toInteger $ ord c 
  in case l of
    Char c    -> pure $ mkChar c
    String s  -> flip emitArray (mkChar<$>(s++['\0'])) =<< getFreshStrName
--  Array  x  -> emitArray $ (literal2Stg <$> x)
    Int i     -> pure $ C.Int 32 i
--    Frac f    -> C.Float (LF.Double $ fromRational f)
    x -> error $ show x

-------------------
-- ModuleBuilder --
-------------------
cgFunction :: L.Name -> [(IName, [TyHead])] -> [(IName , LT.Type)]
  -> (CGBodyEnv s L.Operand) -> [TyHead] -> [FA.FunctionAttribute]
  -> CGEnv s StgWIP
cgFunction llvmNm args free genBody ty attribs = do
  retTy <- cgType ty
  mainArgTys <- (\(i,t) -> (i,) <$> cgType t) `mapM` args
  cgFunction' llvmNm mainArgTys free genBody retTy attribs

cgFunction' :: L.Name -> [(IName, LT.Type)] -> [(IName , LT.Type)]
  -> (CGBodyEnv s L.Operand) -> LT.Type -> [FA.FunctionAttribute]
  -> CGEnv s StgWIP
cgFunction' llvmNm args free genBody retTy attribs = let
  iArgs = fst <$> args ; iFree = fst <$> free ; mainArgTys = snd <$> args
  isDataFn
    | llvmNm == (L.mkName "PrintInt") = True
    | otherwise = False
  -- isDataFn = any isLabelTy mainArgTys
  in do
  let freeVarsStruct = LT.ptr $ LT.StructureType False (snd<$>free)
      argTys = mainArgTys
  (params , blocks) <- runIRBuilderT emptyIRBuilder $ do
    retPtr     <- L.LocalReference (LT.ptr retTy) <$> freshName "retPtr"
    freeStruct <- L.LocalReference freeVarsStruct <$> freshName "FVs"
    freeArgs   <- zipWithM (\ix i -> loadIdx freeStruct ix `named` "free") [0..] iFree
    localArgs  <- argTys `forM` \ty -> L.LocalReference ty <$> fresh
    modify $ \x -> x
      { envArgs = IM.fromList (zip iArgs localArgs ++ zip iFree freeArgs) : envArgs x }
    genBody >>= \case
      L.ConstantOperand C.TokenNone -> pure ()
      x -> if isDataFn
           then store' retPtr x
           else ret x
    modify $ \x -> x { envArgs = drop 1 (envArgs x) }
    let addRet = if isDataFn then (retPtr:) else id
        ars = addRet $ case iFree of
          [] -> localArgs
          _  -> freeStruct : localArgs
    pure ars

  let fnParams = (\(L.LocalReference ty nm) -> Parameter ty nm []) <$> params
      retType = if isDataFn then LT.VoidType else retTy
      fnDef = L.GlobalDefinition L.functionDefaults
        { name        = llvmNm
        , parameters  = (fnParams , False)
        , returnType  = retType
        , basicBlocks = blocks
        , functionAttributes = Right <$> attribs
        }
      argTys' = (\(L.LocalReference ty _nm)->ty) <$> params
      funty = LT.ptr $ LT.FunctionType retType argTys' False
      fnOp  = L.ConstantOperand $ C.GlobalReference funty llvmNm
  emitDef fnDef
  pure $ LLVMFn iFree fnOp

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

----------
-- Data --
----------
mkLabel :: Integer -> [Term] -> CGBodyEnv s L.Operand
mkLabel label tts = do
  l <- flip named "l" $ (`bitcast` tyLabel)
    =<< mkStruct Nothing . (\s -> L.ConstantOperand (C.Null tySplitTree) : constI32 label : s)
    =<< (cgTerm `mapM` tts)
  pure l

mkSTCont stNext fList = mkStruct (Just tySTCont') [stNext , tagSTCont , fList]
mkSTAlts alts  = mkStruct (Just tySTAlts') [(L.ConstantOperand (C.Null tySplitTree)) , tagSTAlts , alts]

-- Avoid generating a splitTree
splitEager label match = _

-- ! it is crucial that tag orders match here and when reducing splittrees
mkSplitTree :: L.Type -> Term -> IM.IntMap Expr -> Maybe Expr -> CGBodyEnv s L.Operand
mkSplitTree retTy label labelMap _defaultFn = let
  mkAlt (CoreFn ars free term _ty) = do
    let iFree = IS.toList free
    freeVars <- lookupArg `mapM` iFree
    let splitNm = "splitFn"
    nm <- L.mkName . (splitNm++) . show <$> lift getFreshSplit
    let freeTys  = zipWith (\i op -> (i , LT.typeOf op)) iFree freeVars
        genBody  = do
          arTys <- lift $ (cgType . snd) `mapM` ars
          retPtr <- lookupArg (-1)
          rawL   <- lookupArg (-2)
          let l = rawL
          l <- bitcast rawL (LT.ptr $ LT.StructureType False (tySplitTree : intType : arTys))
          let getLocal i ix = (i,) <$> (load' =<< (l `gep` [constI32 0 , constI32 (1+ix)]))
          locals <- zipWithM getLocal (fst<$>ars) [1..fromIntegral (length ars)]
          modify $ \x->x{ envArgs = (head (envArgs x) `IM.union` IM.fromList locals) : drop 1 (envArgs x) }
          store' retPtr =<< cgTerm term
          retVoid
          pure $ L.ConstantOperand C.TokenNone
    f <- fnOp <$> lift (cgFunction' nm [(-1, LT.ptr retTy) , (-2,tyLabel)] freeTys genBody LT.VoidType [])
    case freeVars of
      []  -> mkStruct Nothing $ [tagAltFn , f]
      ars -> mkStruct Nothing $ [tagAltPAp , f , constI32 (fromIntegral $ length freeVars)] -- ++ freeVars
  in do
  alts <- flip named "alts" $ (`bitcast` LT.ptr tyAltMap) =<< mkPtrList =<< (mkAlt `mapM` (IM.elems labelMap))
  st   <- mkSTAlts alts
  evalSplitTree retTy st =<< cgTerm label
--case label of
--  f `App` x -> _
--  l         -> evalSplitTree retTy st =<< cgTerm label

----------------------
-- Eval Split trees --
----------------------
evalSplitAlts :: L.Operand -> L.Operand -> L.Operand -> CGBodyEnv s L.Operand
evalSplitAlts retPtr stAlts l = let -- tyAltMap , tyLabel
    splitType = polyFnType
  in mdo
  -- STAlts
  tag    <- flip named "tag"  $ (l `loadIdx` 1)
  alt    <- flip named "alts" $ load' =<< (stAlts `gep` [tag])
  altTag <- flip named "altTy"$ (alt `loadIdx` 0)
  let fnBranch = do
        altF <- loadIdx alt 1 `named` "SF"
        altF `call` [(retPtr,[]),(l,[])]
--    papBranch = do
--      altF <- loadIdx alts 1 `named` "SF"
--      freeVarPtr <- loadIdx alts 2 `named` "free"
--      altF `call` [(retPtr,[]),(freeVarPtr,[]) , (l,[])]
--      load' retPtr
  mkBranchTable False altTag [("fn" , fnBranch)] -- , ("pap" , papBranch)]

genEvalSplitTree :: L.Operand -> L.Operand -> L.Operand -> CGBodyEnv s L.Operand
genEvalSplitTree retPtr st label = do
  stTag  <- flip named "stTag" $ loadIdx st 1
  -- branchTable
  let altsBranch = do
        stAlts <- (`loadIdx` 2) =<< bitcast st tySTAlts
        evalSplitAlts retPtr stAlts label
      contBranch = do
        st'    <- bitcast st tySTCont
        stNext <- loadIdx st' 0
        contFn <- loadIdx st' 2
        storeIdx label 0 stNext
        contFn `call` [(retPtr,[]) , (label,[])]
      branches =
        [ ("evalSTAlts" , altsBranch)
        , ("evalSTCont" , contBranch)]
  mkBranchTable False stTag branches
--load' retPtr

-- eval splitTree fns
evalSplitTreeNm = L.mkName "evalSplitTree"
evalSplitTreeFnTy = LT.FunctionType LT.VoidType evalSTArgTys False
evalSTArgTys = [voidPtrType , tySplitTree , tyLabel]
evalSplitTreeFn = L.ConstantOperand $ C.GlobalReference (LT.ptr $ evalSplitTreeFnTy) evalSplitTreeNm
mkEvalSplitTreeFn :: CGEnv s ()
mkEvalSplitTreeFn = let
 retTy = LT.VoidType
 body   = do
   retPtr <- lookupArg(-1)
   st     <- lookupArg(-2)
   lab    <- lookupArg(-3)
   genEvalSplitTree retPtr st lab
   retVoid
   pure $ L.ConstantOperand C.TokenNone
 in () <$ cgFunction' evalSplitTreeNm (zip [-1,-2,-3] evalSTArgTys) [] body LT.VoidType []

evalSplitTree :: LT.Type -> L.Operand -> L.Operand -> CGBodyEnv s L.Operand
evalSplitTree retTy st l = do
  retPtr   <- alloca' retTy Nothing
  retPtr'  <- bitcast retPtr voidPtrType
  st'      <- bitcast st tySplitTree
--storeIdx st' 0 retPtr'
  call evalSplitTreeFn $ (,[]) <$> [retPtr' , st' , l]
  load' retPtr
