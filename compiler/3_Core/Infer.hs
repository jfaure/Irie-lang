-- : see "Algebraic subtyping" by Stephen Dolan https://www.cs.tufts.edu/~nr/cs257/archive/stephen-dolan/thesis.pdf
module Infer (judgeModule) where
import Prim ( PrimInstr(MkPAp) )
import Builtins (typeOfLit)
import BiUnify ( bisub )
import qualified ParseSyntax as P
import CoreSyn as C
import CoreUtils
import TTCalculus ( ttApp )
import Scope
import Errors
import Externs
import TypeCheck ( check )
import TCState
import Typer (generalise)
import Control.Lens
import Data.Functor.Foldable
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector.Generic.Mutable as MV (unsafeGrowFront)
import qualified BitSetMap as BSM ( toList, fromList, fromListWith, singleton )
--import PrettyCore

--addBind :: Expr -> P.FnDef -> Expr
--addBind jm newDef = jm

judgeModule :: P.Module -> BitSet -> ModuleIName -> Externs.Externs -> V.Vector LoadedMod -> (Expr , Errors)
judgeModule pm importedModules modIName exts loaded = runST $ do
  letBinds' <- MV.new 32
  bis'      <- MV.new 0xFFF
  g         <- MV.new 0
  let scopeparams = initParams importedModules emptyBitSet -- open required
      bindings    = scopeTT exts modIName scopeparams (pm ^. P.bindings)
  (modTT , st) <- runStateT (cata inferF bindings) TCEnvState
    { _externs  = exts
    , _loadedMs = loaded
    , _thisMod  = modIName

    , _letBinds = letBinds'
    , _letNest  = 0
    , _errors   = emptyErrors
    , _bruijnArgVars = mempty
    , _bindStack = []

    , _openModules = importedModules
    , _tmpFails = []
    , _blen     = 0
    , _bis      = bis'
    , _lvls     = []

    , _freeLimit = 0
    , _letCaptures = 0

    , _recursives = 0
    , _nquants = 0
    , _genVec = g
    }
  pure (modTT , st ^. errors)

-- infer >> generalise >> check annotation
-- This stacks inference of forward references and let-binds and identifies mutual recursion
judgeBind :: Int -> IName -> TCEnv s Expr
judgeBind letDepth bindINm = let
  inferParsed :: MV.MVector s (Either P.FnDef Bind) -> P.FnDef -> TCEnv s Expr
  inferParsed wip' abs = freshBiSubs 1 >>= \[tvarIdx] -> do -- [tvarIdx] <- freshBiSubs 1
    bindStack %= ((letDepth , bindINm) :)
    MV.write wip' bindINm (Right (Guard emptyBitSet tvarIdx))
    svlc  <- letCaptures <<.= 0
--  svArgTVs <- use bruijnArgVars
--  freshFreeTVs <- freshBiSubs (V.length svArgTVs)
--  bruijnArgVars .= V.fromList freshFreeTVs

    atLen <- V.length <$> use bruijnArgVars -- all capturable vars (reference where the letCaptures are valid bruijns)
    expr <- cata inferF (P._fnRhs abs) --  traceM $ "inferring: " <> show bindINm

    -- bisub free-vars
--  argTVs <- bruijnArgVars <<.= svArgTVs
--  V.zipWithM biSubTVarTVar (V.take (V.length svArgTVs) svArgTVs) (V.fromList freshFreeTVs)

    lc <- fmap (atLen ,) $ letCaptures <<%= (.|. svlc)
    bindStack %= drop 1

    -- generalise
    MV.read wip' bindINm >>= \case -- learn which binds had to be inferred as dependencies
      Right b@BindOK{} -> pure (bind2Expr b)
      Right (Guard ms tVar) -> do
        when (tVar /= tvarIdx) (error $ show (tVar , tvarIdx))
--      typeAnn <- getAnnotationType (P._fnSig abs)

        -- level mutuality: let a = { f = b.g } ; b = { g = a.f }
        -- check if any prev binds mutual with this one at its level
        let refs = setNBits bindINm .&. ms
        hasMutual <- let isMut i = MV.read wip' i <&> \case { Right (Guard ms _) -> refs .&. ms /= 0 ; _ -> False }
          in anyM isMut (bitSet2IntList refs)
        if hasMutual
          then Core (Var (VQBind (mkQName letDepth bindINm))) (tyVar tVar)
           <$ MV.write wip' bindINm (Right (Mut expr ms lc tVar))
           <* bisub (exprType expr) (tyVar tVar) -- ! recursive => bisub with -τ (itself)
          -- can generalise once all mutuals & associated tvars are fully constrained
          else genExpr wip' expr lc tVar
      b -> error $ "panic: " <> show b

  -- reference to inference stack (forward ref | recursive | mutual)
  preInferred :: MV.MVector s (Either P.FnDef Bind) -> Bind -> TCEnv s Expr
  preInferred wip bind = case bind of
    BindOK _ _f e  -> pure e -- don't inline the expr
    Mut e _ms lc tvar -> genExpr wip e lc tvar
    -- Stacked bind means this was either Mutual | recursive (also weird recursive: r = { a = r })
    Guard mutuals tvar -> do
      -- mark as stacked on top of all binds at this lvl
      -- mark it as mutual with all bind at its level
      bStack <- use bindStack
      let mbs = intList2BitSet $ snd <$> filter ((letDepth == ) . fst) bStack
      (Core (Var (VQBind (mkQName letDepth bindINm))) (tyVar tvar))
        <$ MV.write wip bindINm (Right $ Guard (mutuals .|. mbs) tvar)
    b -> error (show b)

  genExpr :: MV.MVector s (Either P.FnDef Bind) -> Expr -> (Int , BitSet) -> Int -> TCEnv s Expr
  genExpr wip' (Core t ty) letCapture tvarIdx = do
    lvl0 <- use lvls <&> fromMaybe (error "panic empty lvls") . head
    gTy  <- generaliseVar lvl0 tvarIdx ty --  checkAnnotation ann gTy
    let retExpr = Core t gTy
    retExpr <$ MV.write wip' bindINm (Right $ BindOK optInferred letCapture retExpr)

  in use letBinds >>= (`MV.read` letDepth) >>= \wip -> (wip `MV.read` bindINm) >>=
    (inferParsed wip ||| preInferred wip) -- >>= \r -> r <$ (use bindStack >>= \bs -> when (null bs) (clearBiSubs 0))

generaliseVar lvl0 var ty = do
  _cast <- use bis >>= \v -> (v `MV.read` var) <&> _mSub >>= \case
    TyGround [] -> BiEQ <$ MV.write v var (BiSub ty (TyGround []))
    _t -> bisub ty (tyVar var) -- ! recursive => bisub with -τ (itself)
  generalise lvl0 (Left var)
  -- <* when (free == 0 && null (drop 1 ms)) (clearBiSubs recTVar) -- ie. no mutuals and no escaped vars

-- Prefer user's type annotation (it probably contains type aliases) over the inferred one
-- ! we may have inferred some missing information in type holes
checkAnnotation :: Type -> Type -> TCEnv s Type
checkAnnotation annTy inferredTy =
--unaliased <- normaliseType mempty annTy
  check _exts inferredTy annTy >>= \ok -> if ok
  then pure annTy
  else inferredTy <$ (errors . checkFails %= (CheckError inferredTy annTy:))

inferF :: P.TTF (TCEnv s Expr) -> TCEnv s Expr
inferF = let
 withBruijnArgTVars :: Int -> TCEnv s a -> TCEnv s ([Type] , a)
 withBruijnArgTVars n go = freshBiSubs n >>= \argTVars -> do
   w <- (\v -> MV.unsafeGrowFront v n) =<< V.unsafeThaw =<< use bruijnArgVars
   imapM_ (MV.write w) argTVars

   (bruijnArgVars .=) =<< V.unsafeFreeze w
   (reverse $ map tyVar argTVars , ) <$> go <* (bruijnArgVars %= V.drop n)

  -- App is the only place typechecking can fail
 biUnifyApp fTy argTys = freshBiSubs 1 >>= \[retV] ->
   (, tyVar retV) <$> bisub fTy (prependArrowArgsTy argTys (tyVar retV))

 retCast rc tt@(Core f ty) = case rc of { BiEQ -> tt ; c -> Core (Cast c f) ty }

 checkFails srcOff x = use tmpFails >>= \case
   [] -> pure x
   x  -> poisonExpr <$ (tmpFails .= []) <* (errors . biFails %= (map (BiSubError srcOff) x ++))

 inferApp srcOff f args = let
   castRet :: BiCast -> ([Term] -> BiCast -> [Term]) -> Expr -> Expr
   castRet biret castArgs = \case
     Core (App f args) retTy -> case biret of
       CastApp _ac (Just pap) rc -> -- partial application TODO use argcasts
         retCast rc (Core (App (Instr (MkPAp (length pap))) (f : castArgs args biret)) retTy)
       CastApp _ac Nothing    rc -> retCast rc (Core (App f (castArgs args biret)) retTy)
       _ -> Core (App f args) retTy
     t -> t
   -- TODO This will let slip some bieq casts on function arguments
   castArg (a :: Term) = \case { BiEQ -> a ; CastApp [BiEQ] Nothing BiEQ -> a ; cast -> Cast cast a }
   castArgs args' cast = case cast of
     CastApp ac _maybePap _rc -> zipWith castArg args' (ac ++ repeat BiEQ)
     BiEQ -> args'
     _    -> _

   in if any isPoisonExpr (f : args) then pure poisonExpr else do
     (biret , retTy) <- biUnifyApp (exprType f) (exprType <$> args)
     use tmpFails >>= \case
       [] -> castRet biret castArgs <$> ttApp retTy (\i -> judgeBind _0 i) f args -- >>= checkRecApp
       x  -> poisonExpr <$ -- trace ("problem fn: " <> show f :: Text)
         ((tmpFails .= []) *> (errors . biFails %= (map (\biErr -> BiSubError srcOff biErr) x ++)))

 judgeLabel qNameL exprs = let
   labTy = TyGround [THTyCon $ THTuple $ V.fromList (exprType <$> exprs)]
   es = exprs <&> \(Core t _ty) -> t
   in Core (Label qNameL es) (TyGround [THTyCon $ THSumTy $ BSM.singleton (qName2Key qNameL) labTy])

 getQBind q = use thisMod >>= \m -> if modName q == m -- binds at this module are at let-nest 0
   then judgeBind 0 (unQName q) <&> \(Core _t ty) -> Core (Var (VLetBind q)) ty -- don't inline at this stage
   else use loadedMs >>= \ls -> case readQName ls (modName q) (unQName q) of
     Imported e -> pure e
     x -> error (show x)

 -- Setup new freeVars env within a letNest ; should surround this with an inc of letNest, but not the inExpr
 newFreeVarEnv :: forall s a. TCEnv s a -> TCEnv s a
 newFreeVarEnv go = do
   fl   <- use bruijnArgVars <&> V.length
   svFL <- freeLimit <<.= fl
   bl <- use blen
   lvls %= \case -- enter lvl: all prev vars are escaped => if biunified with new vars must export new vars
     []      -> [setNBits bl]
     l0 : ls -> (setNBits bl .|. l0) : l0 : ls

   r <- go

   lvls %= drop 1 -- leave Lvl (? .|. head into next lvl?)
   freeLimit .= svFL
   letCaptures %= (`shiftR` (fl - svFL)) -- diff all let-captures
   pure r

 withLetNest go = letNest <<%= (1+) >>= \nest -> go nest <* (letNest %= \x -> x - 1)

 inferBlock :: V.Vector P.FnDef -> Maybe (TCEnv s Expr) -> TCEnv s (Expr , V.Vector (LetMeta , Bind))
 inferBlock letBindings go = withLetNest $ \nest -> do
   newFreeVarEnv $ do
     use letBinds >>= \lvl -> V.thaw (Left <$> letBindings) >>= MV.write lvl nest
     judgeBind nest `mapM_` [0 .. V.length letBindings - 1]

   -- regeneralise block `mapM_` [0 .. V.length letBindings - 1]
   r <- fromMaybe (pure poisonExpr) go -- in expr
   lets <- use letBinds >>= \lvl -> MV.read lvl nest >>= V.unsafeFreeze
     <&> map (BindUnused . show @P.FnDef ||| identity)
   mI <- use thisMod
   pure (r , V.zipWith (\fn e -> (LetMeta (fnINameToQName mI fn) (fn ^. P.fnNm) (-1) , e)) letBindings lets)

 fnINameToQName mI fnDef = case P._fnRecType fnDef of
   P.LetTuple -> mkQName 0 (P._fnIName fnDef)
   _ -> mkQName mI (P._fnIName fnDef)

 mkFieldCol a b = TyGround [THFieldCollision a b]

 in \case
  P.QuestionF -> pure $ Core Question tyBot
  P.WildCardF -> pure $ Core Question tyBot
  -- letin Nothing = module / record, need to type it
  P.LetInF (P.Block _ _ lets) Nothing ->
    use thisMod >>= \mI -> inferBlock lets Nothing <&> \(_ , lets) -> let -- [(LetMeta , Bind)]
    nms = lets <&> qName2Key . letName . fst
--  nms = lets <&> qName2Key . mkQName mI . iName . fst -- [qName2Key (mkQName (ln + 1) i) | i <- [0..]]
    tys = lets <&> exprType . bind2Expr . snd
    -- letnames = qualified on let-nests + 
    blockTy = THProduct (BSM.fromListWith mkFieldCol $ V.toList $ V.zip nms tys) -- TODO get the correct INames
    in Core (LetBlock lets) (TyGround [THTyCon blockTy])
  P.LetInF (P.Block _ _ lets) pInTT -> inferBlock lets pInTT <&> \(Core t ty , lets) -> Core (LetBinds lets t) ty

  P.VarF v -> case v of -- vars : lookup in appropriate environment
    P.VBruijn b -> do
      argTVars <- use bruijnArgVars
      fLimit <- use freeLimit
      let lvl = V.length argTVars
          diff = lvl - fLimit
          bruijnAtBind = b - diff -- Bruijn idx at the let-binding
      when (b >= diff) (letCaptures %= (`setBit` bruijnAtBind))
      pure $ Core (VBruijn b) (tyVar $ argTVars V.! b)
    P.VLetBind q -> judgeBind (modName q) (unQName q) <&> \(Core _t ty) -> Core (Var (VLetBind q)) ty
    P.VExtern e  -> error $ "Unresolved VExtern: " <> show e
    P.VBruijnLevel l -> error $ "unresolve bruijnLevel: " <> show l

  P.ForeignF{} {- isVA i tt-} -> error "not ready for foreign"
--  tt <&> \(Core _ttExpr ty) -> Core (Var (VForeign i)) ty

  P.BruijnLamF (P.BruijnAbsF argCount argMetas _nest rhs) ->
    withBruijnArgTVars argCount rhs <&> \(argTVars , Core term retTy) -> if argCount == 0 then Core term retTy else
      let fnTy = prependArrowArgsTy argTVars retTy
          alignArgs :: These (IName, Int) Type -> (Int, Type)
          alignArgs = these ((,tyBot) . fst) ((-1,)) (\(i , _) b -> (i , b)) -- TODO argMetas should match argCount
      in  Core (BruijnAbsTyped argCount term (alignWith alignArgs argMetas argTVars) retTy) fnTy

  P.AppF fTT argsTT  -> fTT  >>= \f -> sequence argsTT >>= inferApp (-1) f
  P.PExprAppF _prec q argsTT -> getQBind q >>= \f -> sequence argsTT >>= inferApp (-1) f
  P.RawExprF t -> t
  P.MixfixPoisonF t -> poisonExpr <$ (tmpFails .= []) <* (errors . mixfixFails %= (t:))
  P.QVarF q -> getQBind q
--VoidExpr (QVar QName) (PExprApp p q tts) (MFExpr Mixfixy)

  P.TupleIdxF f tt -> tt >>= \(Core tuple tupleTy) -> freshBiSubs 1 >>= \[i] -> let
    qN = f -- qName2Key (mkQName 0 f) -- (-1 - f))
    expectedTy = TyGround [THTyCon $ THProduct (BSM.singleton qN (tyVar i))]
    in bisub tupleTy expectedTy <&> \cast ->
      let obj = TTLens tuple [qN] LensGet in Core (case cast of { BiEQ -> obj ; cast -> Cast cast obj }) (tyVar i)
  P.TTLensF o tt fieldsLocal maybeSet -> tt >>= \record -> use thisMod >>= \iM -> let
    fields = fieldsLocal -- readField ext <$> fieldsLocal
    recordTy = exprType record
    mkExpected :: Type -> Type
    mkExpected dest = foldr (\f ty -> TyGround [THTyCon $ THProduct (BSM.singleton (qName2Key $ mkQName iM f) ty)]) dest fields
--  mkExpected dest = foldr (\f ty -> TyGround [THTyCon $ THProduct (BSM.singleton f ty)]) dest fields
    in checkFails o =<< case record of
    Core object objTy -> case maybeSet of
      P.LensGet    -> freshBiSubs 1 >>= \[i] -> bisub recordTy (mkExpected (tyVar i)) <&> \cast ->
        let obj = case cast of { BiEQ -> object ; cast -> Cast cast object }
        in Core (TTLens obj fields LensGet) (tyVar i)

      -- LeafTy -> Record -> Record & { path : LeafTy }  (+ for mergeTypes since this is output)
      P.LensSet x  -> x <&> \leaf@(Core _newLeaf newLeafTy) ->
        -- freshBiSubs 1 >>= \[i] -> bisub recordTy (mkExpected tyVar i)
        Core (TTLens object fields (LensSet leaf)) (mergeTypes True objTy (mkExpected newLeafTy))

      P.LensOver x -> x >>= \fn -> do
         (ac , rc , outT , rT) <- freshBiSubs 3 >>= \[inI , outI , rI] -> let
           inT = tyVar inI ; outT = tyVar outI
           in do -- need 3 fresh TVars since we cannot assume anything about the "fn" or the "record"
           argCast <- bisub (exprType fn) (TyGround [THTyCon $ THArrow [inT] outT]) <&> \case
             CastApp [argCast] _pap BiEQ  -> argCast -- pap ?
             BiEQ                         -> BiEQ
             x -> error (show x)
           -- note. the typesystem does not atm support quantifying over field presences
           rCast <- bisub recordTy (mergeTVar rI (mkExpected inT))
           pure (argCast , rCast , outT , rI)

         let lensOverCast = case rc of
               CastProduct _drops [(asmIdx , _cast)] -> Cast (CastOver asmIdx ac fn outT) object
               BiEQ -> object
               _ -> error $ "expected CastProduct: " <> show rc

         pure $ Core lensOverCast (mergeTVar rT (mkExpected outT))

  -- TODO when to force introduce local label vs check if imported
  P.LabelF localL tts -> use thisMod >>= \thisM -> sequence tts 
    <&> judgeLabel (mkQName thisM localL) -- (readLabel ext localL)
  P.QLabelF q -> {-sequence tts <&>-} pure (judgeLabel q [])
 -- sumTy = THSumTy (BSM.singleton (qName2Key q) (TyGround [THTyCon $ THTuple mempty]))

  -- Sumtype declaration
--P.GadtF alts -> use externs >>= \ext -> do
--  let getTy = fromMaybe (TyGround [THPoison]) . tyExpr
--      mkLabelCol a b = TyGround [THLabelCollision a b]
--  sumArgsMap <- alts `forM` \(l , tyParams , _gadtSig@Nothing) -> do
--    params <- tyParams `forM` \t -> getTy <$> t
--    pure (qName2Key (readLabel ext l) , TyGround [THTyCon $ THTuple $ V.fromList params])
--  pure $ Core (Ty (TyGround [THTyCon $ THSumTy $ BSM.fromListWith mkLabelCol sumArgsMap])) (TySet 0)

  P.MatchBF pscrut caseSplits catchAll -> pscrut >>= \(Core scrut gotScrutTy) -> do
      let convAbs :: Expr -> (Term , Type) = \(Core t ty) -> (t , ty)
      (labels , elems) <- sequenceA caseSplits <&> unzip . BSM.toList . fmap convAbs
      def <- sequenceA catchAll <&> fmap convAbs
      let (alts , _rawAltTs) = unzip elems
          branchTys = elems <&> \case
            (BruijnAbsTyped _ _ _ retTy , _) -> retTy -- alts are functions of their label params
            (_ , ty) -> ty
          retTy  = mergeTypeList False $ maybe branchTys ((: branchTys) . snd) def -- ? TODO why negative merge
          altTys = alts <&> \case
            BruijnAbsTyped _ _t ars _retTy -> TyGround [THTyCon $ THTuple (V.fromList $ snd <$> ars)]
            _x -> TyGround [THTyCon $ THTuple mempty]
          scrutSum = BSM.fromList (zip labels altTys)
          scrutTy  = TyGround [THTyCon $ case def of
            Nothing          -> THSumTy scrutSum
            Just (_ , defTy) -> THSumOpen scrutSum defTy]
          matchTy = TyGround (mkTyArrow [scrutTy] retTy)
      (b , retT) <- biUnifyApp matchTy [gotScrutTy]
      case b of { BiEQ -> pure () ; _ -> error "expected bieq" }
      pure $ Core (CaseB scrut retT (BSM.fromList (zip labels alts)) (fst <$> def)) retT

  P.InlineExprF e -> pure e
  P.LitF l           -> pure $ Core (Lit l) (TyGround [typeOfLit l])
  P.ScopePoisonF e   -> poisonExpr <$ (tmpFails .= []) <* (errors . scopeFails %= (e:))
  P.DesugarPoisonF t -> poisonExpr <$ (tmpFails .= []) <* (errors . unpatternFails %= (t:))
  P.ScopeWarnF w t   -> (errors . scopeWarnings %= (w:)) *> t
  x -> error $ "not implemented: inference of: " <> show (embed $ P.Question <$ x)
