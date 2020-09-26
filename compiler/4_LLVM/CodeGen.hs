module CodeGen (mkStg) where
import Prim
import Prim2LLVM
import Externs
import CoreSyn
import CoreUtils
import PrettyCore
import Control.Monad.ST.Lazy
import Control.Monad.State.Lazy
import Control.Monad.Primitive (PrimMonad,PrimState,primitive)
import Data.Functor
import Data.Function
import Data.Foldable
import Data.Char
import Data.Maybe
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
mkStg externBindings coreBinds = let
  nBinds = V.length coreBinds
  moduleDefs = runST $ do
    v <- V.thaw (TWIP <$> coreBinds)
    fns' <- MV.new (MV.length v)
    llvmDefs <$> execStateT (mkEvalSplitTreeFn *> (cgBind `mapM` [0 .. nBinds-1])) CGState {
        wipBinds = v
      , externs  = externBindings
      , llvmDefs =
        (\x -> L.TypeDefinition (structName x) (Just $ rawStructType x)) `map` builtinStructs
        ++
        [ L.TypeDefinition typeDefLabel (Just tyLabel')
        , L.TypeDefinition typeDefAltMap (Just tyAltMap')
        , L.TypeDefinition typeDefSplitTree (Just tySplitTree')
        , L.TypeDefinition typeDefSTAlts (Just tySTAlts')
--      , L.TypeDefinition typeDefSTCont (Just tySTCont')
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
      , moduleUsedNames = M.empty
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

getRetPtr, getTailST :: CGBodyEnv s (Maybe L.Operand)
getRetPtr = gets $ (IM.!? (-900000)) . head . envArgs
getTailST = gets $ (IM.!? (-900001)) . head . envArgs

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
  m@(Match ty labels d) ->
--  let body = cgTerm $ m `App` [Var $ VArg (-100)]
--  in do
--    retTy <- lift $ cgType ty
--    fnOp <$> lift (cgFunction' "Match" [(-100,tyLabel)] [] body retTy []) -- TODO freshname for match -- TODO freeVars
    error $ "floating match" -- mkSplitTree Nothing labels d
  List  args       -> _
  x -> error $ "MkStg: not ready for term: " ++ show x

cgApp :: Term -> [Term] -> CGBodyEnv s L.Operand
cgApp f args = case f of
  Instr i    -> cgInstrApp i args
  Match ty ls d -> case args of
    [x] -> case x of
      App{} -> do
        error $ "passdown st !"
        retTy <- lift (cgType ty)
        st <- mkSplitTree retTy Nothing ls d
        pure st
        -- TODO passdown ST !
      _ -> do -- execute match directly on label
        retTy <- lift (cgType ty)
        lab <- cgTerm x
        mkSplitTree retTy (Just lab) ls d
    _   -> panic $ "Match must have 1 argument"
  f -> cgTerm f >>= \f' -> if isDataFn f'
    then case args of
      []  -> panic "impossible"
      [oneArg] -> let
        collectCont funList = \case
          endArgs@[fPrev `App` argsPrev] -> cgTerm fPrev >>= \fPrev' -> if isDataFn fPrev'
            then collectCont (fPrev' : funList) argsPrev
            else pure (funList , endArgs)
          endArgs -> pure (funList , endArgs)
        in do
          (funList , end) <- collectCont [f'] args
          st <- mkSTCont (mkNullPtr tySplitTree) (reverse funList)
          [label] <- cgTerm `mapM` end -- TODO HACK
--        let retTy = L.resultType . L.pointerReferent . LT.typeOf $ f'
--        if isLabelTy retTy
--        then pure st
--        else evalSplitTree retTy st label
          evalSplitTree intType st label
      args -> mkSTZipper f' =<< (cgTerm `mapM` args)
    else call' f' =<< (cgTerm `mapM` args)

-- mainllArgs <- cgTerm `mapM` args
-- llArgs <- if isDataFn -- may need to tail call a split-tree
--   then do
--     st <- getTailST <&> fromMaybe (panic "tail callable split-tree not in scope")
--     retPtr <- getRetPtr <&> fromMaybe (panic "retPtr not in scope")
--     pure $ retPtr : st : mainllArgs
--   else pure mainllArgs
-- f1 `call` (map (,[]) llArgs)

--retData  = isLabelTy . L.resultType . L.pointerReferent . LT.typeOf
isDataFn = any isLabelTy . L.argumentTypes . L.pointerReferent . LT.typeOf
isLabelTy x = case x of
  LT.PointerType{} -> case LT.pointerReferent x of
    LT.NamedTypeReference nm -> nm==L.mkName "label"
    _ -> False
  _ -> False

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
  [THExt 1 , _] -> pure $ intType
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
  THExt i       -> gets externs >>= (cgType . tyExpr . (V.! i))
  THSum   ls    -> pure $ tyLabel
  THSplit ls    -> pure $ tyLabel
  THProd p      -> pure $ voidPtrType
  THRec{}       -> pure $ tyLabel -- voidPtrType -- HACK
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
    String s  -> flip emitArray (mkChar<$>(s++['\0'])) =<< freshTopName "str"
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
  let isDataFn = isLabelTy retTy || any isLabelTy (snd<$>mainArgTys) -- ie. does it return data ?
  cgFunction' llvmNm isDataFn mainArgTys free genBody retTy attribs

cgFunction' :: L.Name -> Bool -> [(IName, LT.Type)] -> [(IName , LT.Type)]
  -> (CGBodyEnv s L.Operand) -> LT.Type -> [FA.FunctionAttribute]
  -> CGEnv s StgWIP
cgFunction' llvmNm isDataFn args free genBody retTy attribs = let
  iArgs = fst <$> args ; iFree = fst <$> free ; argTys = snd <$> args
  freeVarsStruct = LT.ptr $ LT.StructureType False (snd<$>free)
  in do
  (params , blocks) <- runIRBuilderT emptyIRBuilder $ do
    retPtr     <- L.LocalReference voidPtrType    <$> freshName "retPtr"
    tailST     <- L.LocalReference tySplitTree    <$> freshName "tailST"
    freeStruct <- L.LocalReference freeVarsStruct <$> freshName "FVs"
    freeArgs   <- zipWithM (\ix i -> loadIdx freeStruct ix `named` "free") [0..] iFree
    localArgs  <- argTys `forM` \ty -> L.LocalReference ty <$> fresh
    let normalArgMap = zip iArgs localArgs ++ zip iFree freeArgs
        argMap = if isDataFn then (-900000,retPtr) : (-900001,tailST) : normalArgMap
                 else normalArgMap
    modify $ \x -> x { envArgs = IM.fromList argMap : envArgs x }
    genBody >>= \case
      L.ConstantOperand C.TokenNone -> retVoid
      x -> ret x
    modify $ \x -> x { envArgs = drop 1 (envArgs x) }
    let addRet = if isDataFn then ((retPtr:) . (tailST:)) else id
        ars = addRet $ case iFree of
          [] -> localArgs
          _  -> freeStruct : localArgs
    pure ars

  -- emit the function
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
    =<< mkStruct Nothing . (\s -> constI32 label : s)
    =<< (cgTerm `mapM` tts)
  pure l

mkSTCont stNext fList = do
  let opSz = constI32 (fromIntegral $ length fList)
  fnPtrs <- (`bitcast` LT.ptr dataFnType) =<< mkPtrList dataFnType fList
  mkStruct (Just $ rawStructType stCont) [stNext , tagSTCont , opSz , opSz ,  fnPtrs]

mkSTAlts alts = mkStruct (Just tySTAlts') [mkNullPtr tySplitTree , tagSTAlts , alts]

mkSTZipper fn args = mkStruct (Just tySTAlts')
 $ [mkNullPtr tySplitTree , tagSTZipper , fn] ++ args

-- Avoid generating a splitTree
splitEager label match = _

-- ! it is crucial that tag orders match here and when reducing splittrees
mkSplitTree :: L.Type -> Maybe L.Operand -> IM.IntMap Expr -> Maybe Expr -> CGBodyEnv s L.Operand
mkSplitTree retTy label labelMap _defaultFn = let
  mkAlt (CoreFn ars free term ty) = do
    let iFree = IS.toList free
        isDataFn = isLabelTy retTy
    freeVars <- lookupArg `mapM` iFree
    nm <- lift $ freshTopName (if isDataFn then "SplitCont" else "splitFn")
    let freeTys  = zipWith (\i op -> (i , LT.typeOf op)) iFree freeVars
        genBody  = do
          arTys  <- lift $ (cgType . snd) `mapM` ars
          retPtr  <- lookupArg (-1)
          tailSplit <- lookupArg (-2) -- TODO use
          rawL   <- lookupArg (-3)
          l <- bitcast rawL (LT.ptr $ LT.StructureType False (intType : arTys))
          let getLocal i ix = (i,) <$> loadIdx l ix -- (l `gep` [constI32 0 , constI32 ix]))
          locals <- zipWithM getLocal (fst<$>ars) [1..fromIntegral (length ars)]
          modify $ \x->x{
            envArgs = (head (envArgs x) `IM.union` IM.fromList locals) : drop 1 (envArgs x) }
          result <- cgTerm term
          if   isDataFn
          then void $ evalSplitTree' retPtr tailSplit result -- TODO is ok ??
          else store' retPtr result

          pure $ L.ConstantOperand C.TokenNone

    altFnPtr <- let args = [(-1,LT.ptr retTy) , (-2, tySplitTree) , (-3,tyLabel)]
      in fnOp <$> lift (cgFunction' nm False args freeTys genBody LT.VoidType [])
    case freeVars of
      []  -> mkStruct Nothing $ [tagAltFn , altFnPtr]
      ars -> mkStruct Nothing $ [tagAltPAp , altFnPtr] -- ++ freeVars
  in do
  alts <- ((`bitcast` tyAltMap) <=< mkAlt) `mapM` IM.elems labelMap
  stAlts <- (`bitcast` LT.ptr tyAltMap) =<< mkPtrList (tyAltMap) alts
  tailST <- getTailST <&> fromMaybe (L.ConstantOperand $ C.Null tySplitTree)
  case label of
    Nothing -> mkSTAlts stAlts
    Just l  -> getRetPtr >>= \case
      Just r -> evalSplitAlts r tailST stAlts l
      _      -> do
        retPtr <- (`bitcast` voidPtrType) =<< alloca' retTy Nothing
        evalSplitAlts retPtr tailST stAlts l
        load' retPtr

----------------------
-- Eval Split trees --
----------------------
evalSplitAlts :: L.Operand -> L.Operand -> L.Operand -> L.Operand -> CGBodyEnv s L.Operand
evalSplitAlts retPtr stNext stAlts l = let -- tyAltMap , tyLabel
    splitType = polyFnType
  in mdo
  -- STAlts
  tag    <- flip named "tag"  $ (l `loadIdx` 0)
  alt    <- flip named "alts" $ load' =<< (stAlts `gep` [tag]) -- HACK
  altTag <- flip named "altTy"$ (alt `loadIdx` 0)
  let fnBranch = do
        altF <- loadIdx alt 1 `named` "SF"
        altF `call` map (,[]) [retPtr , stNext , l]
--    papBranch = do
--      altF <- loadIdx alts 1 `named` "SF"
--      freeVarPtr <- loadIdx alts 2 `named` "free"
--      altF `call` [(retPtr,[]),(freeVarPtr,[]) , (l,[])]
--      load' retPtr
  mkBranchTable False altTag [("fn" , fnBranch)] -- , ("pap" , papBranch)]

genEvalSplitTree :: L.Operand -> L.Operand -> L.Operand -> CGBodyEnv s L.Operand
genEvalSplitTree retPtr st label = do
  stTag  <- flip named "stTag" $ loadIdx st 1
  stNext <- st `loadIdx` 0
  -- branchTable
  let altsBranch = do
        stAlts <- (`loadIdx` 2) =<< bitcast st tySTAlts
        evalSplitAlts retPtr stNext stAlts label
      contBranch = do
        st'      <- bitcast st (structAliasType stCont)
        lastIdx  <- loadIdx st' (getFieldIdx stCont "idx")
        contFns  <- loadIdx st' (getFieldIdx stCont "contFns")
        idx      <- sub lastIdx (constI32 1)
        contFn   <- load' =<< (contFns `gep` [idx])
        isEnd    <- icmp IP.EQ idx (constI32 0)
        mdo -- eval the continuation and set-up the next one
          condBr isEnd end cont

          end <- block `named` "contEnd"
          count <- loadIdx st' (getFieldIdx stCont "count")
          storeIdx st' (getFieldIdx stCont "idx") count
          contFn `call` map (,[]) [retPtr, stNext, label]
          br final

          cont <- block `named` "cont"
          storeIdx st' (getFieldIdx stCont "idx") idx
          contFn `call` map (,[]) [retPtr, st, label]
          br final

          final <- block `named` "final"
          pure $ L.ConstantOperand C.TokenNone

      branches =
        [ ("evalSTAlts" , altsBranch)
        , ("evalSTCont" , contBranch)]
  mkBranchTable False stTag branches

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
 in () <$ cgFunction' evalSplitTreeNm False (zip [-1,-2,-3] evalSTArgTys) [] body LT.VoidType []

evalSplitTree :: LT.Type -> L.Operand -> L.Operand -> CGBodyEnv s L.Operand
evalSplitTree retTy st l = do
  retPtr <- gets ((IM.!? (-900000)) . head . envArgs) >>= \case
    Nothing -> alloca' retTy Nothing
    Just r  -> pure r
  evalSplitTree' retPtr st l

evalSplitTree' :: L.Operand -> L.Operand -> L.Operand -> CGBodyEnv s L.Operand
evalSplitTree' retPtr st l = do
  retPtr'  <- bitcast retPtr voidPtrType
  st'      <- bitcast st tySplitTree
  l'       <- bitcast l tyLabel
--storeIdx st' 0 retPtr'
  call evalSplitTreeFn $ (,[]) <$> [retPtr' , st' , l']
  load' retPtr
