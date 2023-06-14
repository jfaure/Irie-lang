-- : see "Algebraic subtyping" by Stephen Dolan https://www.cs.tufts.edu/~nr/cs257/archive/stephen-dolan/thesis.pdf
module Infer (judgeModule) where
import Prim ( PrimInstr(MkPAp) , Literal(..) )
import Builtins (typeOfLit)
import BiUnify
import qualified ParseSyntax as P
import CoreSyn as C
import CoreUtils
import qualified Scope
import Errors
import Externs
import TypeCheck ( check )
import TCState
import Generalise (generalise)
import Control.Lens
import Data.Functor.Foldable
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified BitSetMap as BSM -- ( toList, fromList, fromVec, fromListWith, singleton, unzip )

--addBind :: Expr -> P.FnDef -> Expr
--addBind jm newDef = jm

-- lift lets:
-- 1. rm LetIn Nothing
-- 2. read/write everything to modBinds vec isntead of letBinds/letNest
-- 3. rm VLetNames: mkQName thisMod (translate name)
-- ? mutu
judgeModule :: P.Module -> BitSet -> ModuleIName -> Externs.Externs -> V.Vector LoadedMod -> (ModuleBinds , Errors)
judgeModule pm importedModules modIName exts loaded = let
  letCount = pm ^. P.parseDetails . P.letBindCount
  binds = pm ^. P.bindings
  topBindsCount = V.length binds
  scopeParams' = Scope.initModParams importedModules emptyBitSet (toList (binds <&> (^. P.fnIName))) -- TODO Rm toList
  -- sadly have to dup codepath for this warning: letBinds vectors stops the hylo (infer cata must setup some things)
  warnTopDups :: forall s. TCEnv s ()
  warnTopDups = let topDups = Scope.findDups (binds <&> (^. P.fnIName))
    in when (topDups /= 0) ((\e -> errors . scopeFails %= (e:)) $ LetConflict modIName topDups)
  inferModule :: TCEnv s ModuleBinds
  inferModule = inferBlock 0 binds Nothing >>= \(_inExpr , _lets) -> use modBinds >>= V.freeze
  in runST $ do
  modBinds' <- MV.new (letCount + topBindsCount)
  letBinds' <- MV.new 0xFFF -- let-nest TODO HACK
  bis'      <- MV.new 0xFFF
  g         <- MV.new 0
  (_2 %~ (^. errors)) <$> runStateT (inferModule <* warnTopDups) TCEnvState
    { _externs  = exts
    , _loadedMs = loaded
    , _thisMod  = modIName

    , _modBinds = modBinds'
    , _letBinds = letBinds'
    , _letNest  = 0
    , _errors   = emptyErrors

    , _inferStack = 0
    , _cyclicDeps = 0
    , _topBindsCount = topBindsCount
    , _scopeParams = scopeParams'
    , _bindsBitSet = 0
    , _bruijnArgVars = mempty
    , _tmpFails = []
    , _blen     = 0
    , _bis      = bis'
    , _freeLimit = 0
    , _letCaptures = 0
    , _captureRenames = g
    }

-- infer >> generalise >> check annotation
-- This stacks inference of forward references and let-binds and identifies mutual recursion
judgeBind :: forall s. Int -> IName -> IName -> TCEnv s Expr
judgeBind letDepth bindINm modBindName = use modBinds >>= \modBinds' -> use thisMod >>= \modIName -> let
  -- reference to inference stack (forward ref | recursive | mutual)
  preInferred :: (LetMeta , Bind) -> TCEnv s Expr
  preInferred (lm , bind) = let noop t = Core (Var (letBindIndex lm)) t
    in case bind of
    BindOK _ e  -> pure (noop (exprType e))
    BindRenameCaptures _ _ e -> pure (noop (exprType e))
    Guard tvar -> (cyclicDeps %= (`setBit` modBindName)) $> Core (Captures (letBindIndex lm)) (tyVar tvar)
    Mutu _ _ tvar -> (cyclicDeps %= (`setBit` modBindName)) $> Core (Captures (letBindIndex lm)) (tyVar tvar)

  inferParsed :: P.FnDef -> TCEnv s Expr
  inferParsed abs = freshBiSubs 1 >>= \[tvarIdx] -> do
    -- setup recursion/mutual guards and capture detection
    inferStack %= (`setBit` modBindName)
    let bindIdx = VQBindIndex (mkQName modIName modBindName)
        letMeta = LetMeta (letDepth == 0) (mkQName modIName (abs ^. P.fnIName)) bindIdx (abs ^. P.fnSrc)
    MV.write modBinds' modBindName (letMeta , Guard tvarIdx) -- recs/mutuals will biunify with our tvar
    svlc  <- letCaptures <<.= 0
    argVars <- use bruijnArgVars
    atLen <- V.length <$> use bruijnArgVars -- all capturable vars (reference where the letCaptures are valid bruijns)
    (captureRenames .=) =<< MV.new atLen

    -- run inference, need to solve scopes on top bindings (letdepth 0):
    -- the infer part of (hypo infer scopeApo) can't see through LetBind vectors, so per top-bind will fuse more
    expr <- case letDepth of
      0 -> use scopeParams >>= \sp -> use externs >>= \exts -> use topBindsCount >>= \tc ->
          hypo inferF (Scope.scopeApoF tc exts modIName) (abs ^. P.fnRhs , sp)
      _ -> cata inferF (abs ^. P.fnRhs) -- let-binds were already scoped, since they depend on nesting context

    lcVars <- letCaptures <<%= (.|. svlc)
    freeVarCopies <- use captureRenames >>= \cr -> reverse (bitSet2IntList lcVars) `forM`
      \l -> (argVars V.! l ,) <$> MV.read cr l

    -- level mutuality: let a = { f = b.g } ; b = { g = a.f }
    -- "is" are backward refs depending on this binding; if this bind depends on any of them, they are mutual
    is <- use inferStack
    cycles <- use cyclicDeps
    if (cycles .&. clearBit is modBindName /= 0) && head (bitSet2IntList cycles) /= Just modBindName
    then MV.write modBinds' modBindName (letMeta , Mutu expr lcVars tvarIdx)
--    *> traceShowM ("mutu: " , modBindName , bitSet2IntList is , bitSet2IntList cycles)
      $> Core (Captures (letBindIndex letMeta)) (tyVar tvarIdx)
    else do
      let mutuals = is .&. complement (setNBits modBindName)
--    traceShowM ("generalise: " , modBindName , bitSet2IntList mutuals , bitSet2IntList is , bitSet2IntList cycles)
      inferStack %= (.&. complement mutuals)
      cyclicDeps %= (.&. complement mutuals)

      -- Mutuals must be fully constrained then all generalised together
      (mFree , mutus) <- fmap unzip $ bitSet2IntList (clearBit mutuals modBindName) `forM` \mut ->
        MV.read modBinds' mut <&> \(mLetMeta , Mutu mExpr mFree mtv) -> (mFree , (mut , mLetMeta , mExpr , mtv))
      let unionFree = lcVars -- TODO
          unionFreeVarCopies = snd <$> freeVarCopies -- TODO
          tvs = ((tvarIdx , exprType expr) :) $ mutus <&> \(_,_,mexpr,t) -> (t , exprType mexpr)
      -- generalise reads from tvarIdx , also recursive functions/mutuals must be bisubbed with themselves
      use bis >>= \v -> tvs `forM_` \(tvarIdx , ty) -> (v `MV.read` tvarIdx) <&> _mSub >>= \case
        TyGround [] -> BiEQ <$ MV.write v tvarIdx (BiSub ty (TyGround []))
        _t -> bisub ty (tyVar tvarIdx) -- ! recursive => bisub with -τ (itself)

      mutus `forM_` \(mb , mlm , mexpr , mtv) ->
        genExpr mb mlm (exprTerm mexpr) unionFreeVarCopies (atLen , unionFree) mtv
      genExpr modBindName letMeta (exprTerm expr) unionFreeVarCopies (atLen , unionFree) tvarIdx
--    <* clearBiSubs tvarIdx
      <* when (is == 0) (clearBiSubs 0)

  in use bindsBitSet >>= \b -> if testBit b modBindName
    then MV.read modBinds' modBindName >>= preInferred
    else (bindsBitSet %= (`setBit` modBindName))
      *> use letBinds >>= (`MV.read` letDepth) >>= \wip -> (wip `MV.read` bindINm)
      >>= inferParsed

genExpr :: IName -> LetMeta -> Term -> [Int] -> (Int , BitSet) -> Int -> TCEnv s Expr
genExpr modBindName lm term freeVarCopies (atLen , freeVars) tvarIdx = use modBinds >>= \modBinds' -> let
  rawTy = prependArrowArgsTy (tyVar <$> freeVarCopies) (tyVar tvarIdx)
  in use blen >>= \bl -> use bis >>= \bis' ->
    lift (generalise bl bis' rawTy) >>= \gTy -> let
    rawRetExpr = Core term gTy -- Core (if freeVars == 0 then t else BruijnAbs (popCount freeVars) t) gTy
    noInlineExpr = let q = Var (letBindIndex lm) in
      Core (if freeVars == 0 then q else BruijnAbs (popCount freeVars) q) gTy
    bind = if freeVars == 0
    then BindOK optInferred rawRetExpr
    else BindRenameCaptures atLen freeVars rawRetExpr -- Recursive binds need their free-env backpatched in
  in noInlineExpr <$ MV.write modBinds' modBindName (lm , bind)

-- judgeBind then uninline and add + biunify any captured arguments
getModBind letNest letName modBindName = do
  expr <- judgeBind letNest letName modBindName
  use modBinds >>= (`MV.read` modBindName) <&> snd >>= \case
    BindOK{} -> pure expr
    BindRenameCaptures atLen free _ -> 
--    when ({-popCount (lc + 1) /= 0-} lc /= setNBits ld) (traceM "TODO rename captured VBruijns") *>
      explicitFreeVarApp atLen free expr -- ld doesn't matter since we dont β-reduce
    _ -> pure expr -- TODO handle mutuals that capture vars ; ie. spawn mutumorphisms

explicitFreeVarApp :: Int -> BitSet -> Expr -> TCEnv s Expr
explicitFreeVarApp _atLen lc e@(Core t ty) = if lc == 0 then pure e else let
  bruijnArs = reverse $ bitSet2IntList lc {-[atLen - 1 , atLen - 2 .. 0] -} 
  appFree = App t (VBruijn <$> bruijnArs)
  in do
  atvs <- use bruijnArgVars
  (cast , appTy) <- biUnifyApp ty (tyVar . (atvs V.!) <$> bruijnArs)
  pure (retCast cast (Core appFree appTy))
  -- trace (prettyTermRaw t <> "\n" <> prettyTermRaw (exprTerm c) <> "\n" <> prettyTyRaw ty) c

-- Prefer user's type annotation (it probably contains type aliases) over the inferred one
-- ! TODO we may have inferred some missing information in type holes
checkAnnotation :: Type -> Type -> TCEnv s Type
checkAnnotation inferredTy annTy = check inferredTy annTy >>= \case
  True  -> pure annTy
  False -> inferredTy <$ (errors . checkFails %= (CheckError inferredTy annTy:))

-- App is the only place inference can fail (if an arg doesn't subtype its expected type)
biUnifyApp :: Type -> [Type] -> TCEnv s (BiCast , Type)
biUnifyApp fTy argTys = freshBiSubs 1 >>= \[retV] ->
  (, tyVar retV) <$> bisub fTy (prependArrowArgsTy argTys (tyVar retV))

-- Infer a block
withLetNest go = letNest <<%= (1+) >>= \nest -> go nest <* (letNest %= \x -> x - 1)

 -- Setup new freeVars env within a letNest ; should surround this with an inc of letNest, but not the inExpr
newFreeVarEnv :: forall s a. TCEnv s a -> TCEnv s a
newFreeVarEnv go = do
  fl   <- use bruijnArgVars <&> V.length
  svFL <- freeLimit <<.= fl
  go <* do
    freeLimit .= svFL
    letCaptures %= (`shiftR` (fl - svFL)) -- reset relative to next enclosing let-nest

inferBlock :: Int -> V.Vector P.FnDef -> Maybe (TCEnv s Expr) -> TCEnv s (Expr , V.Vector (LetMeta , Bind))
inferBlock liftNames letBindings inExpr = withLetNest $ \nest -> do
  newFreeVarEnv $ do
    use letBinds >>= \lvl -> V.thaw letBindings >>= MV.write lvl nest
    [0 .. V.length letBindings - 1] `forM_` \i -> judgeBind nest i (liftNames + i)
  ret <- fromMaybe (pure poisonExpr) inExpr
  lets <- use modBinds >>= \v -> V.freeze (MV.slice liftNames (V.length letBindings) v) -- freeze copies it
  pure (ret , lets)

retCast rc tt@(Core f ty) = case rc of { BiEQ -> tt ; c -> Core (Cast c f) ty }

inferF :: P.TTF (TCEnv s Expr) -> TCEnv s Expr
inferF = let
 withBruijnArgTVars :: Int -> TCEnv s a -> TCEnv s ([Type] , a)
 withBruijnArgTVars n go = freshBiSubs n >>= \argTVars -> do
   (bruijnArgVars %= (V.fromList argTVars <>))
   (reverse $ tyVar <$> argTVars , ) <$> go <* (bruijnArgVars %= V.drop n)

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
       [] -> pure $ castRet biret castArgs (Core (App (exprTerm f) (exprTerm <$> args)) retTy)
       x  -> poisonExpr <$ ((tmpFails .= [])
         *> (errors . biFails %= (map (BiSubError srcOff) x ++)))

 judgeLabel qNameL exprs = let
   labTy = TyGround [THTyCon $ THTuple $ V.fromList (exprType <$> exprs)]
   es = exprs <&> \(Core t _ty) -> t
   in Core (Label qNameL es) (TyGround [THTyCon $ THSumTy $ BSM.singleton (qName2Key qNameL) labTy])

 -- result of mixfix solves; QVar, PExprApp
 getQBind q = use thisMod >>= \m -> if modName q == m -- binds at this module are at let-nest 0
   then unQName q & \i -> getModBind 0 i i
   else use loadedMs <&> \ls -> readQIName ls (modName q) (unQName q)
     & fromMaybe (error (showRawQName q))

 in \case
  P.QuestionF -> pure $ Core Question tyBot
  P.WildCardF -> pure $ Core Question tyBot
  -- letin Nothing = module / record, need to type it
  P.LetInF (P.Block _ _ lets) liftNames pInTT -> use topBindsCount >>= \tc ->
    inferBlock (tc + liftNames) lets (Just pInTT)
    <&> \(Core t ty , _lets) -> Core t ty
--  <&> \(Core t ty , lets) -> Core (Lets (intList2BitSet . toList $ lets <&> unQName . letName . fst) t) ty
  P.ProdF pFields -> let -- duplicate the field name to both terms and types
    mkCore (ts , tys) = Core (Prod ts) (TyGround [THTyCon (THProduct tys)])
    in fmap (mkCore . BSM.unzip . BSM.fromVec)
      $ pFields `forM` \(i , s) -> s <&> \(Core t ty) -> (i , (t , ty))

  P.VParseINameF e  -> error $ "panic: Unresolved IName: " <> show e
  P.VarF v -> case v of -- vars : lookup in appropriate environment
    P.VBruijn b -> do
      argTVars <- use bruijnArgVars
      fLimit <- use freeLimit
      let lvl = V.length argTVars
          diff = lvl - fLimit
          bruijnAtBind = b - diff -- Bruijn idx relative to enclosing let-binding, not current lvl
      tv <- if b >= diff -- if b is free, insertOrRetrieve its local tvar
        then (letCaptures <<%= (`setBit` bruijnAtBind)) >>= \oldLc -> use captureRenames >>= \cr ->
          if testBit oldLc bruijnAtBind
          then MV.read cr bruijnAtBind
          else freshBiSubs 1 >>= \[t] -> t <$ MV.write cr bruijnAtBind t
        else pure (argTVars V.! b) -- local arg
      pure $ Core (VBruijn b) (tyVar tv)
    P.VLetBind (_iName , letNest , letIdx , i) -> getModBind letNest letIdx i
    P.VBruijnLevel l -> error $ "unresolve bruijnLevel: " <> show l

  P.BruijnLamF (P.BruijnAbsF argCount argMetas _nest rhs) ->
    withBruijnArgTVars argCount rhs <&> \(argTVars , Core term retTy) -> if argCount == 0 then Core term retTy else
      let fnTy = prependArrowArgsTy argTVars retTy
          alignArgs :: These (IName, Int) Type -> (Int, Type)
          alignArgs = these ((,tyBot) . fst) ((-1,)) (\(i , _) b -> (i , b)) -- TODO argMetas should match argCount
      in  Core (BruijnAbsTyped argCount term (alignWith alignArgs argMetas argTVars) retTy) fnTy

  P.AppF src fTT argsTT  -> fTT  >>= \f -> sequence argsTT >>= inferApp src f
  P.PExprAppF src _prec q argsTT -> getQBind q >>= \f -> sequence argsTT >>= inferApp src f
  P.RawExprF t -> t
  P.MixfixPoisonF t -> poisonExpr <$ (tmpFails .= []) <* (errors . mixfixFails %= (t:))
  P.MFExprF srcOff m -> let err = MixfixError srcOff ("Lone mixfix word: " <> show m)
    in poisonExpr <$ (tmpFails .= []) <* (errors . mixfixFails %= (err:))
  P.IQVarF q -> getQBind q
  P.QVarF q  -> getQBind q

  P.TupleIdxF qN tt -> tt >>= \(Core tuple tupleTy) -> freshBiSubs 1 >>= \[i] -> let
    expectedTy = TyGround [THTyCon $ THProduct (BSM.singleton qN (tyVar i))]
    in bisub tupleTy expectedTy <&> \cast ->
      let obj = TTLens tuple [qN] LensGet in Core (case cast of { BiEQ -> obj ; cast -> Cast cast obj }) (tyVar i)
  P.TTLensF o tt fieldsLocal maybeSet -> tt >>= \record -> use thisMod >>= \iM -> let
    fields = qName2Key . mkQName iM <$> fieldsLocal
    recordTy = exprType record
    mkExpected :: Type -> Type
    mkExpected dest = foldr (\f ty -> TyGround [THTyCon $ THProduct (BSM.singleton f ty)]) dest fields
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
    <&> judgeLabel (mkQName thisM localL)
  P.QLabelF q -> {-sequence tts <&>-} pure (judgeLabel q [])
 -- sumTy = THSumTy (BSM.singleton (qName2Key q) (TyGround [THTyCon $ THTuple mempty]))

  P.DataF liftedLetStart alts  -> do
    thisM <- use thisMod
    modBinds' <- use modBinds
    tc <- use topBindsCount
    tys <- sequence (alts <&> \(l , params) -> ({-qName2Key (mkQName thisM l)-} l ,) <$> sequence params)
    alts <- let
      doAlt letName (lI , params) = do
        altTy <- params `forM` exprToTy
        let lm = LetMeta False qL (VQBindIndex (mkQName thisM letName)) (-1)
            qL = mkQName thisM lI
            l  = qName2Key qL
            labTy = tHeadToTy $ THTyCon (THTuple (V.fromList altTy))
            arrowTy = tHeadToTy $ THTyCon (THArrow altTy (tHeadToTy $ THTyCon $ THSumTy (BSM.singleton l labTy)))
        MV.write modBinds' letName (lm , BindOK optInferred (Core (Label qL []) arrowTy))
        pure (l , labTy)
      in zipWithM doAlt [tc + liftedLetStart .. ] tys
    pure $ Core (Ty (tHeadToTy $ THTyCon (THSumTy (BSM.fromList alts)))) (TySet 0) -- max of universe in alts

  -- TODO gadt must have a signature for the whole thing also!
--P.GadtF alts -> do
--  sumArgsMap <- alts `forM` \(l , tyParams , _gadtSig@Nothing) -> do
--    params <- tyParams `forM` \t -> t
--    pure (l , TyGround [THTyCon $ THTuple $ V.fromList params])
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
        scrutTy  = TyGround [THTyCon $ if isJust def then THSumOpen scrutSum else THSumTy scrutSum]
        matchTy = TyGround (mkTyArrow [scrutTy] retTy)
    (b , retT) <- biUnifyApp matchTy [gotScrutTy]
    case b of { BiEQ -> pure () ; _ -> error "expected bieq" }
    pure $ Core (CaseB scrut retT (BSM.fromList (zip labels alts)) (fst <$> def)) retT

  P.TypedF t ty    -> t >>= \(Core term gotT) -> ty >>= exprToTy >>= \annTy ->
    use blen >>= \bl -> use bis >>= \bis' -> lift (generalise bl bis' gotT)
      -- Need to clear all tvars
      >>= \genGotTy -> Core term <$> checkAnnotation genGotTy annTy
  P.InlineExprF e -> pure e
  P.LitF l        -> pure $ Core (Lit l) (TyGround [typeOfLit l])
  P.PLitArrayF ls -> pure $ Core (Lit $ LitArray ls) (TyGround [THTyCon $ THArray $ mergeTypeHeadList True (typeOfLit <$> ls)])
  P.PArrayF ls    -> sequence ls <&> \exprs -> unzipExprs exprs & \(elems , tys) ->
    Core (Array (V.fromList elems)) (TyGround [THTyCon $ THArray $ mergeTypeList True tys])
  P.ScopePoisonF e   -> poisonExpr <$ (tmpFails .= []) <* (errors . scopeFails %= (e:))
  P.DesugarPoisonF t -> poisonExpr <$ (tmpFails .= []) <* (errors . unpatternFails %= (t:))
  P.ScopeWarnF w t   -> (errors . scopeWarnings %= (w:)) *> t
  P.ForeignF{} {- isVA i tt-} -> error "not ready for foreign"
--  tt <&> \(Core _ttExpr ty) -> Core (Var (VForeign i)) ty
  x -> error $ "not implemented: inference of: " <> show (embed $ P.WildCard <$ x)
