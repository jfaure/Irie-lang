-- : see "Algebraic subtyping" by Stephen Dolan https://www.cs.tufts.edu/~nr/cs257/archive/stephen-dolan/thesis.pdf
module Infer (judgeModule) where
import Prim ( PrimInstr(MkPAp) , Literal(..) )
import Builtins (typeOfLit)
import BiUnify
import qualified ParseSyntax as P
import CoreSyn as C
import CoreUtils
import TTCalculus ( ttApp )
import Scope
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
  scopeParams' = initModParams importedModules emptyBitSet (toList (binds <&> (^. P.fnIName))) -- TODO Rm toList
  inferModule :: TCEnv s ModuleBinds
  inferModule = inferBlock 0 binds Nothing >>= \(_inExpr , _lets) -> use modBinds >>= V.freeze
  in runST $ do
  modBinds' <- MV.new (letCount + topBindsCount)
  letBinds' <- MV.new 0xFFF -- let-nest TODO HACK
  bis'      <- MV.new 0xFFF
  g         <- MV.new 0
  (_2 %~ (^. errors)) <$> runStateT inferModule TCEnvState
    { _externs  = exts
    , _loadedMs = loaded
    , _thisMod  = modIName
    , _openModules = importedModules

    , _modBinds = modBinds'
    , _letBinds = letBinds'
    , _letNest  = 0
    , _errors   = emptyErrors

    , _inferStack = 0
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
  inferParsed :: P.FnDef -> TCEnv s Expr
  inferParsed abs = freshBiSubs 1 >>= \[tvarIdx] -> do -- [tvarIdx] <- freshBiSubs 1
    inferStack %= (`setBit` modBindName) --  bindStack %= ((letDepth , bindINm) :)
    let letMeta = LetMeta (letDepth == 0) (mkQName modIName (abs ^. P.fnIName)) (abs ^. P.fnNm) (-1)
    MV.write modBinds' modBindName (letMeta , Guard emptyBitSet tvarIdx)
    svlc  <- letCaptures <<.= 0
    argVars <- use bruijnArgVars
    atLen <- V.length <$> use bruijnArgVars -- all capturable vars (reference where the letCaptures are valid bruijns)
    (captureRenames .=) =<< MV.new atLen

    rawExpr <- case letDepth of -- need to solve scopes on top bindings:
      -- the hypo (scopeApo) can't see through LetBinds vectors, so doing it per module bind is way more optimal
      0 -> use scopeParams >>= \sp -> use externs >>= \exts ->
          use thisMod >>= \modIName -> use topBindsCount >>= \tc ->
          hypo inferF (scopeApoF tc exts modIName) (abs ^. P.fnRhs , sp)
      _ -> cata inferF (abs ^. P.fnRhs)

--  inferStack %= (`clearBit` modBindName) --  bindStack %= drop 1
    lcVars <- letCaptures <<%= (.|. svlc)
    argTVs <- use captureRenames >>= \cr -> bitSet2IntList lcVars `forM` \l -> (argVars V.! l ,) <$> MV.read cr l
    let freeVarCopies = snd <$> argTVs :: [Int]
        lc = (atLen , lcVars)
        expr = if True || lcVars == 0 then rawExpr else
          rawExpr & \(Core t ty) -> Core t (prependArrowArgsTy (tyVar <$> freeVarCopies) ty)

    -- generalise: Collect mutuals by learning which binds had to be inferred as dependencies
    MV.read modBinds' modBindName >>= \case
      (_ , b@BindOK{}) -> pure (bind2Expr b)
      (lm , Guard ms tVar) -> do
        when (tVar /= tvarIdx) (error $ show (tVar , tvarIdx))
--      typeAnn <- getAnnotationType (P._fnSig abs)

        -- level mutuality: let a = { f = b.g } ; b = { g = a.f }
        -- check if any prev binds mutual with this one at its level
        let refs = setNBits modBindName .&. ms
        hasMutual <- let isMut i = MV.read modBinds' i <&> (\case { Guard ms _ -> refs .&. ms /= 0 ; _ -> False }) . snd
          in anyM isMut (bitSet2IntList refs)
        if hasMutual
          then Core (Var (VQBind (mkQName modIName modBindName))) (tyVar tVar)
           <$ MV.write modBinds' modBindName (lm , Mut expr ms lc tVar)
           <* bisub (exprType expr) (tyVar tVar) -- ! recursive => bisub with -τ (itself)
           <* when (not (null freeVarCopies)) (error "mutual free vars")
          -- can generalise once all mutuals & associated tvars are fully constrained
          else genExpr lm expr freeVarCopies lc tVar
      b -> error $ "panic: " <> show b

  -- reference to inference stack (forward ref | recursive | mutual)
  preInferred :: (LetMeta , Bind) -> TCEnv s Expr
  preInferred (lm , bind) = case bind of
    BindOK _ _f e  -> pure e -- don't inline the expr
    Mut e _ms lc tvar -> genExpr lm e [] lc tvar
    -- v Stacked bind means it could be Mutual | recursive (also weird recursive: r = { a = r })
    Guard mutuals tvar -> do
      -- mark as stacked on top of all binds at this lvl
      -- mark it as mutual with all bind at its level
      mbs <- use inferStack
      Core (Var (VQBind (mkQName modIName modBindName))) (tyVar tvar)
        <$ MV.write modBinds' modBindName (lm , Guard (mutuals .|. mbs) tvar)

  genExpr :: LetMeta -> Expr -> [Int] -> (Int , BitSet) -> Int -> TCEnv s Expr
  genExpr lm (Core t ty) freeVarCopies letCapture@(_,freeVars) tvarIdx = do
    gTy  <- do
      _cast <- use bis >>= \v -> (v `MV.read` tvarIdx) <&> _mSub >>= \case
        TyGround [] -> BiEQ <$ MV.write v tvarIdx (BiSub ty (TyGround []))
        _t -> bisub ty (tyVar tvarIdx) -- ! recursive => bisub with -τ (itself)
      let copyFreeVarsTy = prependArrowArgsTy (tyVar <$> freeVarCopies) (tyVar tvarIdx)
      use blen >>= \bl -> use bis >>= \bis' -> lift (generalise bl bis' copyFreeVarsTy)
      -- <* when (free == 0 && null (drop 1 ms)) (clearBiSubs recTVar) -- ie. no mutuals and no escaped vars
    let rawRetExpr = Core (if freeVars == 0 then t else BruijnAbs (popCount freeVars) t) gTy
    retExpr <- pure rawRetExpr -- explicitFreeVarApp freeVars rawRetExpr
    -- TODO Mark eraser args (ie. lazy VBruijn rename for simplifer)
    -- HACK partial letCapture will break β
    (inferStack <%= (`clearBit` modBindName)) >>= \is -> when (is == 0) (clearBiSubs 0)
    retExpr <$ MV.write modBinds' modBindName (lm , BindOK optInferred letCapture retExpr)
  in use bindsBitSet >>= \b -> case testBit b modBindName of
    True  -> MV.read modBinds' modBindName >>= preInferred
    False -> (bindsBitSet %= (`setBit` modBindName))
      *> use letBinds >>= (`MV.read` letDepth)
        >>= \wip -> (wip `MV.read` bindINm) >>= inferParsed

-- judgeBind then uninline and add + biunify any captured arguments
getModBind letNest letName modBindName = do
  modIName <- use thisMod
  expr <- judgeBind letNest letName modBindName <&> \(Core _t ty) ->
    Core (Var (VQBind (mkQName modIName modBindName))) ty -- don't inline at this stage
  use modBinds >>= (`MV.read` modBindName) <&> snd >>= \case
--use letBinds >>= (`MV.read` letDepth) >>= \wip -> (wip `MV.read` modBindName) >>= \case
    b@BindOK{} -> free b & \(_ld , lc) -> explicitFreeVarApp lc expr
      -- ld doesn't matter since we dont β-reduce
    _ -> pure expr -- TODO handle mutuals that capture vars ; ie. spawn mutumorphisms

explicitFreeVarApp :: BitSet -> Expr -> TCEnv s Expr
explicitFreeVarApp lc e@(Core t ty) = if lc == 0 then pure e else let
  bruijnArs = bitSet2IntList lc
  appFree = App t (VBruijn <$> bruijnArs)
  in do
  atvs <- use bruijnArgVars
  (_cast , appTy) <- biUnifyApp ty (tyVar . (atvs V.!) <$> bruijnArs)
  pure (Core appFree appTy)
  -- trace (prettyTermRaw t <> "\n" <> prettyTermRaw (exprTerm c) <> "\n" <> prettyTyRaw ty) c

-- Prefer user's type annotation (it probably contains type aliases) over the inferred one
-- ! we may have inferred some missing information in type holes
checkAnnotation :: Type -> Type -> TCEnv s Type
checkAnnotation annTy inferredTy =
--unaliased <- normaliseType mempty annTy
  check _exts inferredTy annTy >>= \ok -> if ok
  then pure annTy
  else inferredTy <$ (errors . checkFails %= (CheckError inferredTy annTy:))

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

inferF :: P.TTF (TCEnv s Expr) -> TCEnv s Expr
inferF = let
 withBruijnArgTVars :: Int -> TCEnv s a -> TCEnv s ([Type] , a)
 withBruijnArgTVars n go = freshBiSubs n >>= \argTVars -> do
   (bruijnArgVars %= (V.fromList argTVars <>))
   (reverse $ tyVar <$> argTVars , ) <$> go <* (bruijnArgVars %= V.drop n)

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
       [] -> castRet biret castArgs <$> ttApp retTy f args -- >>= checkRecApp
       x  -> poisonExpr <$ -- trace ("problem fn: " <> show f :: Text)
         ((tmpFails .= []) *> (errors . biFails %= (map (\biErr -> BiSubError srcOff biErr) x ++)))

 judgeLabel qNameL exprs = let
   labTy = TyGround [THTyCon $ THTuple $ V.fromList (exprType <$> exprs)]
   es = exprs <&> \(Core t _ty) -> t
   in Core (Label qNameL es) (TyGround [THTyCon $ THSumTy $ BSM.singleton (qName2Key qNameL) labTy])

 -- result of mixfix solves
 getQBind q = use thisMod >>= \m -> if modName q == m -- binds at this module are at let-nest 0
   then unQName q & \i -> getModBind 0 i i
   else use loadedMs <&> \ls -> readQName ls (modName q) (unQName q)
     & fromMaybe (error (showRawQName q)) 

 in \case
  P.QuestionF -> pure $ Core Question tyBot
  P.WildCardF -> pure $ Core Question tyBot
  -- letin Nothing = module / record, need to type it
  P.LetInF (P.Block _ _ lets) liftNames pInTT -> use topBindsCount >>= \top ->
    inferBlock (top + liftNames) lets (Just pInTT)
    <&> \(Core t ty , lets) -> Core (LetBinds lets t) ty
  P.ProdF pFields -> let -- duplicate the field name to both terms and types
    mkCore (ts , tys) = Core (Prod ts) (TyGround [THTyCon (THProduct tys)])
    in fmap (mkCore . BSM.unzip . BSM.fromVec)
      $ pFields `forM` \(i , s) -> s <&> \(Core t ty) -> (i , (t , ty))

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
    P.VLetBind (q , i) -> getModBind (modName q) (unQName q) i
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
    <&> judgeLabel (mkQName thisM localL)
  P.QLabelF q -> {-sequence tts <&>-} pure (judgeLabel q [])
 -- sumTy = THSumTy (BSM.singleton (qName2Key q) (TyGround [THTyCon $ THTuple mempty]))

  P.DataF alts  -> do
    thisM <- use thisMod
    tys <- sequence (alts <&> \(l , params) -> (qName2Key (mkQName thisM l) ,) <$> sequence params)
    alts <- tys `forM` \(l , params) -> fmap ((l,) . tHeadToTy . THTyCon . THTuple . V.fromList) $ params `forM` \case
      Core (Ty t) _ -> pure t
--    Core (App t ty) _ -> ttApp t ty
      notTy    -> pure $ trace ("TODO emit an error for data not being type: " <> show notTy :: Text) tyBot
    pure $ Core (Ty (TyGround [THTyCon (THSumTy (BSM.fromList alts))])) (TySet 0) -- max of universe in alts

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

  P.InlineExprF e -> pure e
  P.LitF l           -> pure $ Core (Lit l) (TyGround [typeOfLit l])
  P.PLitArrayF ls    -> pure $ Core (Lit $ LitArray ls) (TyGround [THTyCon $ THArray $ mergeTypeHeadList True (typeOfLit <$> ls)])
  P.PArrayF ls    -> sequence ls <&> \exprs -> unzipExprs exprs & \(elems , tys) ->
    Core (Array (V.fromList elems)) (TyGround [THTyCon $ THArray $ mergeTypeList True tys])
  P.ScopePoisonF e   -> poisonExpr <$ (tmpFails .= []) <* (errors . scopeFails %= (e:))
  P.DesugarPoisonF t -> poisonExpr <$ (tmpFails .= []) <* (errors . unpatternFails %= (t:))
  P.ScopeWarnF w t   -> (errors . scopeWarnings %= (w:)) *> t
  x -> error $ "not implemented: inference of: " <> show (embed $ P.WildCard <$ x)
