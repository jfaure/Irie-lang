module CodeGen (mkStg) where
import Prim
import Prim2LLVM
import Externs
import CoreSyn
import CoreUtils
import Data.List (partition)
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.Text as T
import qualified Data.IntMap as IM
import qualified Data.Map as M
import qualified LLVM.AST as L
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.FunctionAttribute as FA
import qualified LLVM.AST.Type  as LT
import qualified LLVM.AST.Typed as LT
import           LLVM.AST.Global
import           LLVM.AST.Linkage as L
--import           LLVM.AST.CallingConvention as CC
--import LLVM.IRBuilder.Module hiding (function)
import LLVM.IRBuilder.Monad
import LLVM.IRBuilder.Instruction hiding (gep)

--mkStg :: V.Vector Expr -> V.Vector (HName , Bind) -> V.Vector QTT -> L.Module
mkStg externBindings coreMod@(JudgedModule bindNames coreBinds) = let
  mkVAFn ty nm = L.GlobalDefinition functionDefaults
    { name = L.mkName nm , linkage = L.External , parameters=([],True) , returnType = ty }
  nBinds = V.length coreBinds
  moduleDefs = runST $ do
    v <- V.unsafeThaw (TWIP <$> V.zip bindNames coreBinds) -- ok since (TWIP <$> coreBinds) is a new vector already
    llvmDefs <$> execStateT (cgBind `mapM` [0 .. nBinds-1]) CGState {
        wipBinds = v
--    , externResolver = extResolver
      , externs  = externBindings
      , coreModule = coreMod
      , llvmDefs = [
--      (\x -> L.TypeDefinition (structName x) (Just $ rawStructType x)) `map` builtinStructs ++
          mkVAFn frameType "fralloc_mergeFrames"
        , mkVAFn frameType "fralloc_shareFrames"
        , mkVAFn voidPtrType "fralloc_freeFrame"
        , mkVAFn intType "fralloc_isSingle"
        , mkVAFn voidPtrType "fralloc_newFrag"
        , mkVAFn voidPtrType "fralloc_freeFrag"

        , mkVAFn frameType   "fralloc_DFList_mergeFrames"
        , mkVAFn voidPtrType "fralloc_push"
        , mkVAFn voidPtrType "fralloc_pop"

        , L.TypeDefinition "A"   Nothing
        , L.TypeDefinition "ANY" Nothing
        , L.TypeDefinition "Fr"  Nothing
        , L.GlobalDefinition functionDefaults
          { name=L.mkName "printf"
          , linkage=L.External , parameters=([] , True) , returnType=intType }
        , L.GlobalDefinition functionDefaults
          { name=L.mkName "strtol"
          , linkage=L.External , parameters=([] , True) , returnType=intType }
        , L.GlobalDefinition functionDefaults
          { name=L.mkName "llvm.uadd.with.overflow.i32"
          , linkage=L.External , parameters=([] , True)
          , returnType=LT.StructureType False [intType , LT.IntegerType 1] }
        ]
      , moduleUsedNames = M.empty
      , stack = []
     }
  in L.defaultModule {
      L.moduleName = ""
    , L.moduleDefinitions = reverse $ moduleDefs
--  , L.moduleTargetTriple = Just "x86_64-unknown-linux-gnu" -- x86_64-pc-linux-gnu
--  , L.moduleDataLayout = Just "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
    }

--lookupArg i = gets ((IM.!? i) . regArgs . head . stack)
--  Nothing  -> gets envArgs >>= \e -> panic $ "arg not in scope: " ++ show i ++ "\nin: " ++ show (IM.keys <$> e)

-- Bindings vary from functions to types to constants to constexprs to instructions
cgBind :: IName -> CGEnv s StgWIP
cgBind i = gets wipBinds >>= \wip -> MV.read wip i >>= \case
 TWIP (nm , bind) -> let
   llvmNm = L.mkName (T.unpack nm)
   in mdo -- handle recursive refs using MonadFix
     MV.write wip i b
     b <- case bind of
       BindOK tt -> case tt of
         Core (Instr instr) ty -> STGFn False [] <$>
           emitPrimFunction instr [intType , intType] intType
         Core t ty -> -- panic $ "not ready for constants:\n" ++ show tt
           dataFunction llvmNm [] [] t ty [] <&> \case
             STGFn _ [] op -> STGConstant op
             f -> f
           -- TODO ? llvm.global_ctors: appending global [ n x { i32, void ()*, i8* } ]
--       CoreFn args free t ty -> dataFunction llvmNm args [] t ty []
         Ty ty -> LLVMTy <$> cgType ty
       ko -> error "panic Core failed to generate a valid binding"
     pure b
 x -> pure x

-- DataFunctions pass extra frame arguments with their data args
dataFunction :: L.Name -> [(IName, [TyHead])] -> [(IName , LT.Type)]
  -> Term -> [TyHead] -> [FA.FunctionAttribute]
  -> CGEnv s StgWIP
dataFunction llvmNm args free body returnType attribs = let
    iArgs = fst<$>args ; iFree = fst<$>free
    isDataTy = any isDataTyHead
--  retData  = d_ returnType $ d_ llvmNm $ did_ $ isDataTy returnType
    retData  = isDataTy returnType
--  argMap = zip iArgs localArgs ++ zip iFree freeArgs
    (dArgs , rArgs) = partition (isDataTy . snd) args
  in do
  retTy <- cgType returnType
--mainArgTys <- (\(i,t) -> (i,) <$> cgType t) `mapM` args
  rArgTys <- (cgType . snd) `mapM` rArgs
  dArgTys <- (cgType . snd) `mapM` dArgs
--d_ (show llvmNm) (pure ())

  (params , blocks) <- runIRBuilderT emptyIRBuilder $ do
    -- give the sret the first fresh name if it's needed
    let getSRet = fromMaybe (panic $ T.pack $ "fn returns data, which contradicts it's type: " ++ show returnType)
    rParams <- rArgTys `forM` \ty -> L.LocalReference ty <$> fresh
    dParams <- dArgTys `forM` \ty -> do
      frNm <- fresh
      opNm <- fresh
      pure $ DataArg 0 (L.LocalReference frameType frNm) (L.LocalReference ty opNm)
    modify $ \x -> x {
     stack = CallGraph
     { regArgs  = IM.fromList$zip (fst<$>rArgs) rParams
     , dataArgs = IM.fromList$zip (fst<$>dArgs) dParams
     , splits = []
     } : stack x }

    sret <- cgTerm body >>= \case
      STGOp op Nothing -> Nothing <$ ret op
      STGOp op (Just frame) -> do -- to return the frame to the caller, we need to use a pointer arg
        sret2  <- L.LocalReference (LT.ptr frameType) <$> freshName "retFrame"
        store' sret2 frame *> ret op
        pure $ Just sret2

    modify $ \x -> x { stack = drop 1 (stack x) }
    let opFrPairs = concat $ (\(DataArg _ f o) -> [f , o]) <$> dParams
        pars = rParams ++ opFrPairs
    pure $ case sret of
      Just s  -> s : pars
      Nothing -> pars

  let fnParams = (\(L.LocalReference ty nm) -> Parameter ty nm []) <$> params
  STGFn retData iFree <$> emitFunction llvmNm fnParams retTy blocks

cgTerm' = fmap op . cgTerm
mkSTGOp x = STGOp x Nothing

cgTerm :: Term -> CGBodyEnv s STGOp
cgTerm = let
  cgName = \case
    VBind i -> lift (cgBind i) >>= \case
      STGConstant x -> mkSTGOp <$> x `call'` [] -- TODO where is the frame
      f -> pure $ mkSTGOp $ fnOp f
    -- Args: 1. regular args 2. dataArgs 3. splits from Match
    VArg  i -> gets (fromJust . head . stack) >>= \cg -> case (regArgs cg IM.!? i) of
      Just reg -> pure $ mkSTGOp reg
      Nothing  -> case (dataArgs cg IM.!? i) of
        Just (DataArg shares frame op) -> 
          pure $ STGOp op (Just frame)
        Nothing -> let
          doSplit s = (\op -> (sframe s , op)) <$> (components s IM.!? i)
          in case asum (doSplit <$> splits cg) of
          Just (f , o)  -> pure $ STGOp o (Just f)
          Nothing -> panic $ T.pack $ "arg not in scope: " ++ show i
    VExt  i -> _
  in \case
  Var vNm -> cgName vNm
  Lit l   -> mkSTGOp . L.ConstantOperand <$> lift (literal2Stg l)
  Instr i -> error $ show i -- cgPrimInstr i -- TODO top-level wrapper for instr
--MultiIf ((ifE,thenE):alts) elseE ->  -- convert to tree of switch-cases
--  genSwitch ifE [(C.Int 1 1 , thenE)] . Just $ case alts of
--    [] -> elseE
--    branches -> MultiIf branches elseE

  Cons fields      -> _ -- alloc =<< (cgTerm `mapM` fields)
  Label i tts      -> do -- merge argframes
    rawTerms <- (cgTerm . (\(Core t ty) -> t)) `mapM` tts
    let args  = op <$> rawTerms
        labTy = LT.StructureType False $ sumTagType : (LT.typeOf <$> args)
        sz    = L.ConstantOperand $ C.sizeof labTy
        dFrames = catMaybes $ fr <$> rawTerms
--  frame  <- frAlloc_mergeFrames (constI32 (fromIntegral $ length dFrames) : dFrames)
--  outPtr <- frAlloc_new frame sz
    frame  <- frAlloc_DFList_mergeFrames (constI32 (fromIntegral $ length dFrames) : dFrames)
    outPtr <- frAlloc_push frame sz
    out    <- bitcast outPtr (LT.ptr labTy)
    zipWithM (storeIdx out) [0..length args] (constTag (fromIntegral i) : args)
    pure $ STGOp outPtr (Just frame)

  m@(Match ty labels d) -> -- mkSplitTree Nothing labels d
    panic $ "floating match" -- we need an argument to split on (this should have been lifted to a fn def)
  List  args       -> _

  App f args -> case f of
    Match ty alts d -> case args of
      [scrutCore] -> do
        stgScrut  <- cgTerm scrutCore
        retTy <- lift (cgType ty)
        let frame = fromMaybe (panic "no frame") $ fr stgScrut
            scrut = op stgScrut
        tag    <- load' =<< (`gep` [constI32 0]) =<< bitcast scrut (LT.ptr sumTagType)
        -- each branch is responsible for memory, duping frames etc..
        ourFrame <- frAlloc_isSingle frame -- TODO suspect
        let mkAlt l e = genAlt ourFrame frame scrut l e >>= \(STGOp op maybeD) ->
              bitcast op retTy <&> (`STGOp` maybeD)
            branches = ("",) . uncurry mkAlt <$> (IM.toList alts)
        mkBranchTable tag (C.Int 32 . fromIntegral <$> IM.keys alts) branches
      bad -> panic $ T.pack $ "Match should have exactly 1 argument; not " ++ show (length bad)
    Instr i   -> case i of -- ifThenE is special since it can return data
      IfThenE -> case args of
        [ifE, thenE, elseE] -> cgTerm ifE >>= \(STGOp scrut Nothing) ->
          mkBranchTable scrut [C.Int 1 1 , C.Int 1 0] (zip ["then","else"] [cgTerm thenE, cgTerm elseE])
        -- genSwitch ifE [(C.Int 1 1 , thenE)] (Just elseE)) args
      _ -> mkSTGOp <$> cgInstrApp i args
    Var (VBind fI) -> lift (cgBind fI) >>= \case
      STGFn retData free fptr -> do
        stgops <- cgTerm `mapM` args
        let iterFn [] = Nothing
            iterFn (STGOp x mframe : xs) = case mframe of
              Just frame -> Just (frame , STGOp x Nothing : xs)
              Nothing    -> Just (x , xs)
            args' = unfoldr iterFn stgops
        if retData
        then do
          retFramePtr <- alloca' frameType Nothing
          retOp <- fptr `call'` (retFramePtr : args')
          retFrame <- load' retFramePtr
          pure $ STGOp retOp (Just retFrame)
        else mkSTGOp <$> call' fptr args'
    Var (VArg fI) -> _
    Var (VExt fI) -> _
    f -> panic "STG: floating function; expected binding index"
  --f -> cgTerm f >>= \f' -> call' f' =<< (cgTerm `mapM` args)

  x -> error $ "MkStg: not ready for term: " ++ show x

-- also return the args consumed (Match needs to uniformize this)
genAlt :: L.Operand -> L.Operand -> L.Operand -> ILabel -> Expr -> CGBodyEnv s STGOp
genAlt isOurFrame frame scrut lName (Core (Abs args _free t ty) _ty) = do
  altType <- lift $ LT.ptr . LT.StructureType False . (sumTagType :) <$> (cgType `mapM` (snd <$> args))
  e   <- bitcast scrut altType
  llArgs <- loadIdx e `mapM` [1 .. length args]
  let newSplit = Split lName frame (IM.fromList $ zip (fst<$>args) llArgs)
   in modifySF $ \s->s{ splits = newSplit : splits s }
--frAlloc_freeFrag frame e (L.ConstantOperand $ C.sizeof $ LT.typeOf e) -- TODO too early ? sometimes pointless ?
  frAlloc_pop frame e (L.ConstantOperand $ C.sizeof $ LT.typeOf e) -- TODO too early ? sometimes pointless ?
  r <- cgTerm t
  modifySF $ \x -> x { splits = drop 1 (splits x) }
  pure r

--retData  = isLabelTy . L.resultType . L.pointerReferent . LT.typeOf
--isDataFn = any isLabelTy . L.argumentTypes . L.pointerReferent . LT.typeOf
isDataFn = \case
  Var (VBind i) | i < 5 -> True
  x -> False
isLabelTy x = case x of
  LT.PointerType{} -> case LT.pointerReferent x of
    LT.NamedTypeReference nm -> nm==L.mkName "label"
    _ -> False
  _ -> False

isVoidTy x = case x of { LT.VoidType -> True ; x -> False }

cgInstrApp instr args = case instr of
    PutNbr -> call (L.ConstantOperand (C.GlobalReference (LT.ptr $ LT.FunctionType intType [] True) (L.mkName "printf"))) =<< (map (,[]) <$> cgTerm' `mapM` (Lit (String "%d\n") : args))
    CallExt nm -> let
      llvmNm = L.mkName (T.unpack nm)
      fn = C.GlobalReference (LT.ptr $ LT.FunctionType intType [] True) llvmNm
      in call (L.ConstantOperand fn) =<<  (map (,[]) <$> cgTerm' `mapM` args)
    Zext    -> (\[a] -> zext a intType) =<< (cgTerm' `mapM` args)
    AddOverflow -> _
    i -> let instr = primInstr2llvm i in cgTerm' `mapM` args >>= \ars -> case (i , ars) of
      (PredInstr _ , [a,b]) -> emitInstr boolType (instr a b)
      (Unlink , [fnEnd , fnCont , str]) -> _
      (Link   , [elem , str]) -> _
      (_ , [a,b]) -> emitInstr (LT.typeOf $ fromJust $ head ars) (instr a b)
      x -> panic "arity mismatch on prim instruction"

cgType :: [TyHead] -> CGEnv s L.Type
cgType = \case
  [t] -> cgTypeAtomic t
  [THExt 1 , _] -> pure $ intType
  [_ , THExt 1] -> pure $ intType
  x   -> pure polyType
--x   -> panic $ "lattice Type: " ++ show x

cgTypeAtomic = let
  voidPtrType = polyType -- tyLabel -- LT.ptr $ LT.StructureType False []
  in \case
  THExt i       -> gets externs >>= (cgType . tyExpr . (`readPrimExtern` i))
  THTyCon (THArrow tys t) -> (\ars retTy -> L.FunctionType retTy ars False)
    <$> (cgType `mapM` tys) <*> cgType t
--THVar v    -> gets (did_ . _pSub . (V.! v) . typeVars . coreModule) >>= cgType
--THArg a    -> gets (did_ . _mSub . (V.! a) . argTypes . coreModule) >>= cgType
--THRec r    -> gets (did_ . _pSub . (V.! r) . typeVars . coreModule) >>= cgType
  THVar{} -> pure voidPtrType
--THArg{} -> pure voidPtrType
  x -> pure $ case x of
    THPrim p   -> primTy2llvm p
--  THArray t  -> _ -- LT.ArrayType $ cgType t
--  THSum   ls -> tyLabel
--  THSplit ls -> tyLabel
--  THProd p   -> tyLabel
    THSet  0   -> tyLabel
    x -> error $ "MkStg: not ready for ty: " ++ show x
tyLabel = voidPtrType -- HACK

cgPrimInstr i = case i of
  ExprHole -> _
  MkNum    -> _
  MkReal   -> _
  MkTuple  -> _
  MkPAp{}  -> _
  Alloc    -> _
  Len      -> _
  SizeOf   -> _ -- C.sizeof
  x -> primInstr2llvm x

genSwitch :: Term -> [(C.Constant , Term)] -> Maybe Term -> CGBodyEnv s L.Operand
genSwitch scrutTerm branches defaultBranch = let
  callErrorFn str = _ -- call (errFn str) [] <* unreachable
  genAlt endBlock (scrutVal , expr) = do -- collect (result,block) pairs for the phi instr
    flip (,) <$> block <*> (cgTerm' expr <* br endBlock)
  in mdo
  scrut <- cgTerm' scrutTerm
  switch scrut dBlock (zip (fst <$> branches) (snd <$> retBlockPairs))
  dBlock   <- (block `named`"switchDefault")
  dSsa   <- case defaultBranch of
    Just d  -> cgTerm' d <* br endBlock
    Nothing -> callErrorFn "NoPatternMatch"
  retBlockPairs <- genAlt endBlock `mapM` branches
  endBlock <- block `named` "switchEnd"
  phi $ (dSsa, dBlock) : retBlockPairs

----------------
-- Primitives --
----------------
literal2Stg :: Literal -> CGEnv s C.Constant
literal2Stg l = let
  mkChar c = C.Int 8 $ toInteger $ ord c 
  in case l of
  Char c    -> pure $ mkChar c
  String s  -> flip emitArray (mkChar<$>(s++['\0'])) =<< freshTopName "str"
--Array  x  -> emitArray $ (literal2Stg <$> x)
  Int i     -> pure $ C.Int 32 i
--  Frac f    -> C.Float (LF.Double $ fromRational f)
  x -> error $ show x

-- generate fn for prim instructions (ie. if need a function pointer for them)
emitPrimFunction instr argTys retTy = do
  nm <- freshTopName "instr" -- TODO nah
  (params, blocks) <- runIRBuilderT emptyIRBuilder $ do
    params@[a,b] <- argTys `forM` \ty -> L.LocalReference ty <$> fresh
    ret =<< emitInstr (LT.typeOf a) ((primInstr2llvm instr) a b)
    pure params
  let fnParams = (\(L.LocalReference ty nm) -> Parameter ty nm []) <$> params
  emitFunction nm fnParams retTy blocks

emitFunction :: L.Name -> [Parameter] -> LT.Type -> [L.BasicBlock] -> CGEnv s L.Operand
emitFunction label fnParams retty blocks =
  let def = L.GlobalDefinition L.functionDefaults
        { name        = label
        , parameters  = (fnParams, False)
        , returnType  = retty
        , basicBlocks = blocks
        }
      argTys = (\(Parameter ty nm at)->ty) <$> fnParams
      funty = LT.ptr $ LT.FunctionType retty argTys False
      fnOp = L.ConstantOperand $ C.GlobalReference funty label
  in fnOp <$ emitDef def
