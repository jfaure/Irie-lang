module MkSSA where
import SSA
import Prim
import CoreSyn hiding (Type , Expr)
--import CoreUtils
import ShowCore()
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector as V
import qualified Data.IntMap as IM

type CGEnv s a = StateT (CGState s) (ST s) a
data CGState s = CGState {
   wipBinds    :: MV.MVector s CGWIP
 , typeDef     :: Int -- typedef counter
 , wipTypeDefs :: [Type]
 , top         :: Bool -- for inserting Rets
 , locCount    :: Int
 , argTable    :: MV.MVector s (Expr , Type)
 , muDefs      :: IntMap Int
 , expectedTy  :: Type
 }
addLocal :: CGEnv s Int
addLocal = do
  l <- gets locCount
  modify $ \x->x{locCount = locCount x + 1}
  pure l
newTypeDef :: CGEnv s Int
newTypeDef = gets typeDef >>= \td -> td <$ modify (\x->x{typeDef = td + 1})
addTypeDef :: Type -> CGEnv s Type
addTypeDef td = td <$ modify (\x -> x { wipTypeDefs = td : wipTypeDefs x })
setRetTy ty = modify (\x->x{expectedTy = ty})

data CGWIP
  = WIPCore  (HName , Bind)
--  | WIPConst SSALiteral
  | WIPFn    Function
  | WIPDecl  FunctionDecl
  | WIPTy    IName -- index to typedef map
  deriving Show

charPtr_t = TPrim (PtrTo (PrimInt 8))

setTop t = modify $ \x->x{top = t}

mkSSAModule coreMod@(JudgedModule modIName modName nArgs bindNames pFields pLabels coreBinds) = let
  nArgs  = 100 -- TODO !
  nBinds = V.length coreBinds
  wip2Fn = \case
    WIPFn fn -> fn
    x -> error $ "binding did not codegen: " <> show x
  in runST $ do
    at <- MV.new nArgs
    v  <- V.unsafeThaw (WIPCore <$> V.zip bindNames coreBinds)
    st <- (cgBind `mapM` [0 .. nBinds-1]) `execStateT` CGState {
      wipBinds = v
    , typeDef  = 0
    , wipTypeDefs = []
    , top = True
    , argTable = at
    , locCount = 0
    , muDefs   = mempty
    , expectedTy = TVoid
    }
    fns <- V.unsafeFreeze (wipBinds st)
    pure $ Module modName (V.reverse $ V.fromList $ wipTypeDefs st) mempty (wip2Fn <$> fns)

typeOfInstr i = TPrim (PrimInt 32)

isPolyT = \case { TPoly->True;_->False }
isPolyFnT (TFunction arTs retT) = isPolyT retT || any isPolyT arTs
isFnT = \case { TFunction{}->True ; _ -> False }

getExprType :: Expr -> CGEnv s Type
getExprType = \case
  Arg i -> gets argTable >>= \at -> snd <$> MV.read at i
  Ret e -> getExprType e
  Call (LocalFn i) _ -> do
    decl <- cgBind i <&> \case
      WIPFn   f -> fnDecl f
      WIPDecl d -> d
    pure (TFunction (V.fromList (SSA.args decl)) (retTy decl))

  x -> pure $ case x of
    Call (Prim i) _ -> typeOfInstr i
    Load t _     -> t
    BitCast t _  -> t
    FromPoly t _ -> t
    ToPoly   t _ -> t
    Struct t _   -> t
    LitE l       -> TPrim (PrimInt 32)
    y -> error $ show x

ssaTy :: [TyHead] -> CGEnv s Type
ssaTy = let
  singleT2ssa = \case
    THPrim p  -> pure $ TPrim p
    THTyCon t -> case t of
      THSumTy t   -> mdo
        td <- newTypeDef
        addTypeDef typeDecl -- enforce ordering
        typeDecl <- (TSum td . V.fromList <$> (ssaTy `mapM` IM.elems t))
        pure typeDecl
      THTuple t   -> mdo
        td <- newTypeDef
        addTypeDef typeDecl -- enforce ordering
        typeDecl <- (TStruct td <$> (ssaTy `mapM` t))
        pure typeDecl
      THArrow a r -> TFunction
        <$> (V.fromList <$> (ssaTy `mapM` a))
        <*> ssaTy r
      x -> error $ show x
    THMuBound x -> TRec . (IM.! x) <$> gets muDefs
    THMu x t    -> do
      nm <- gets typeDef -- bit yolo, but we can assume THMu directly contains a struct TODO semi HACK
      modify (\y->y{ muDefs = IM.insert x nm (muDefs y) })
      t <- ssaTy t
      pure t

    THBi y t  -> ssaTy t
    THBound b -> pure TPoly
    THVar x   -> pure $ trace ("warning THVar: " <> show x :: Text) TPoly

    x -> error $ show x
  in \case
  [t] -> singleT2ssa t
  _   -> pure TPoly -- low effort

emitFunction nm i args t ty = gets wipBinds >>= \wip ->
  ssaTy ty >>= \ssaT -> let
  (argTys , retTy) = case ssaT of
    TFunction a r -> (V.toList a , r)
    r             -> (mempty , r)
  ars = zipWith (\(i,_) t -> (i,t)) args argTys
  fd = FunctionDecl nm argTys retTy
  -- add a explicit return; push it down control flow
  addRet e = case e of
    Switch e es d -> Switch e (fmap addRet <$> es) (addRet d)
    Call (Prim IfThenE) (ifE : args) -> Call (Prim IfThenE)
      (ifE : (addRet <$> args))
    _ -> Ret e
  in do
    at <- gets argTable
    ars `forM` \(i , t) -> MV.write at i (Arg i , t)
    MV.write wip i (WIPDecl fd)
    setRetTy retTy
    e <- addRet <$> cgExpr t
    let w = WIPFn (Function fd (maybe 0 fst (head args)) e)
    w <$ MV.write wip i w

cgCore wip i nm b = let
  in setTop True *> case b of
  Core (Abs args free t _ty) ty -> emitFunction nm i args t ty
  Core t ty  -> emitFunction nm i [] t ty
  PoisonExpr -> panic $ "attempted to codegen a poison expr: " <> nm

cgBind i = gets wipBinds >>= \wip -> MV.read wip i >>= \case
  WIPCore (nm , b) -> case b of
    BindOK b    -> cgCore wip i nm b
    BindOpt _ b -> cgCore wip i nm b
--  Ty ty -> pure $ ssaTy ty
  x -> pure x

cgExpr :: Term -> CGEnv s Expr
cgExpr t = let
  cgName = \case
    VBind b -> pure (Extern b) -- fnDecl <$> cgBind b
    VArg  i -> gets argTable >>= \at -> fst <$> MV.read at i
      -- pure $ Arg i
  in case t of
  Var vNm -> cgName vNm
  Lit l   -> pure $ LitE l
  Instr i -> _ -- emitInstrWrapper
  Cast cast term -> cgExpr term >>= doCast cast
  App f args -> setTop False *> cgApp f args

  RecLabel label fixPoints exprs -> mdo
    et  <- exprs `forM` \(Core t ty) -> (,) <$> cgExpr t <*> ssaTy ty
    exp <- gets expectedTy
    let (es , ts) = unzip et
        tagE   = Fin 32 (fromIntegral $ qName2Key label)
        datas  = let
          boxTy = exp -- V.fromList ts V.! fp
          boxElem vals fp =
            V.modify (\v -> MV.modify v (Boxed boxTy) fp) vals
          in V.foldl boxElem (V.fromList es) fixPoints
        dataT  = TTuple (V.fromList ts)
        sumVal = Struct dataT datas
--               BitCast dataT (Struct dataT datas)
        ret = SumData mempty (LitE tagE) sumVal
    pure $ case exp of
      TPoly -> ToPoly exp ret
      _     -> BitCast exp ret
  Label i tts            -> _
  Match ty labels d      -> _
  Cons  fields           -> _
  TTLens tt _fields lens -> cgExpr tt
  x -> error $ "MkSSA: not ready for term: " <> show x

cgApp f ars = case f of
--Match ty alts d | [a] <- ars -> cgExpr a >>= \scrut ->
--  emitMatchApp scrut ty alts d
  RecMatch alts d | [a] <- ars -> cgExpr a >>= \scrut ->
    emitMatchApp scrut alts d
  Instr i -> Call (Prim i) <$> (cgExpr `mapM` ars)
  Var (VBind i) -> do
    decl <- cgBind i <&> \case
      WIPFn   f -> fnDecl f
      WIPDecl d -> d
    exp <- gets expectedTy
    r <- Call (LocalFn i) <$>
      zipWithM (\ty e -> setRetTy ty *> cgExpr e) (SSA.args decl) ars
    pure $ case (exp , retTy decl) of
      (TPoly , TPoly) -> r
      (TPoly , rT)    -> ToPoly rT r
      (eT    , TPoly) -> FromPoly eT r
      (a     , b    ) -> r
  Var{}   -> cgExpr f >>= \case
    x -> error $ show x

doCast cast term = case cast of
  BiEQ        -> pure term
  CastInstr i -> pure $ Call (Prim i) [term]
--CastApp     -> _
  CastProduct drops leaves -> _ --prodCast leaves term
  CastOver asmIdx preCast (Core fn _) retTy -> case term of
    RawFields ty fields -> _

emitMatchApp (Arg i) alts d = do
  (arg , argT) <- gets argTable >>= \at -> MV.read at i
  tys <- case argT of
    TSum typedef ts -> pure ts
  let tag = Extract (sumTag_t) 0 arg
      val = Extract (charPtr_t)  1 arg
  emitMatchApp (SumData tys tag val) alts d
emitMatchApp (SumData sumTy tag val) alts d = let
  emitBranch tag (recs , Core (Abs ars _ body _) t) = gets argTable >>= \at -> let
    branchTy@(TStruct typedef subTys) = sumTy V.! tag
    val' = UnUnion tag branchTy val --BitCast branchTy val
    in case V.length recs of
    0 -> do
      zip ([0..]::[Int]) ars `forM` \(asmIx , (argIx , t)) ->
        MV.write at argIx
          (Extract (subTys V.! asmIx) asmIx val' , (subTys V.! asmIx))
      cgExpr body
    1 -> do
      zip ([0..]::[Int]) ars `forM` \(asmIx , (argIx , t)) ->
       MV.write at argIx $ if asmIx `elem` recs
--      then (Gep   branchTy 1 val' , branchTy)
        then (Load branchTy (Extract branchTy 1 val') , branchTy)
        else (Extract (subTys V.! asmIx) asmIx val' , (subTys V.! asmIx))
      cgExpr body

    n -> _
  in do
    brs <- IM.traverseWithKey emitBranch $ alts
    pure $ Switch tag (IM.toList brs) Void
emitMatchApp x alts d = error $ show x
