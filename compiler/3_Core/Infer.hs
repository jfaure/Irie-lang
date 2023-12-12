-- : see "Algebraic subtyping" by Stephen Dolan https://www.cs.tufts.edu/~nr/cs257/archive/stephen-dolan/thesis.pdf
module Infer (judgeModule) where
import Prim(Literal(..) , typeOfLit)
import qualified ParseSyntax as P
import CoreSyn as C
import CoreUtils (isPoisonExpr , tHeadToTy , mkTyArrow , prependArrowArgsTy , mergeTVar , mergeTypes , mergeTypeList , mergeTypeHeadList , unzipExprs , mergeCaseBranches)
import qualified Scope
import Errors
import Externs (LoadedMod , Externs , readQName)
import TypeCheck ( check )
import TCState
import Control.Lens
import Data.Functor.Foldable
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified BitSetMap as BSM
import PrettyCore

data InferEnv = InferEnv
  { eLoadedMods    :: V.Vector LoadedMod
  , eModIName      :: ModuleIName
  , eExterns       :: Externs
  , eScopeParams   :: Scope.Params
  , eTopBindsCount :: Int
}
judgeModule :: V.Vector LoadedMod -> Externs.Externs -> BitSet -> ModuleIName -> P.Module
  -> ((ModuleBinds , DepPermutation) , Errors)
judgeModule loaded exts importedModules modIName pm = let
  topINames = pm ^. P.parseDetails . P.topINames
  binds     = pm ^. P.bindings
  letCount  = pm ^. P.parseDetails . P.letBindCount
  topBindsCount = V.length binds
  bindsCount = letCount + topBindsCount
  scopeParams' = Scope.initModParams topINames letCount (pm ^. P.imports) importedModules (binds <&> (^. P.fnIName))
  -- sadly have to dup codepath for this warning: letBinds vectors stops the hylo (infer cata must setup some things)
  warnTopDups :: forall s. TCEnv s ()
  warnTopDups = let topDups = Scope.findDups (binds <&> (^. P.fnIName))
    in when (topDups /= 0) ((\e -> errors . scopeFails %= (e:)) (LetConflict modIName topDups))

  inferEnv = InferEnv loaded modIName exts scopeParams' topBindsCount
  inferModule :: TCEnv s (ModuleBinds , DepPermutation)
  inferModule = inferBlock inferEnv 0 binds Nothing
    *> use modBinds >>= V.freeze >>= \mb -> use depOrder >>= V.freeze . snd <&> (mb,)

  in runST do
  modBinds' <- MV.new bindsCount
  depOrder' <- MV.new bindsCount
  letBinds' <- MV.new 0xFFF -- let-nest TODO HACK
  bis'      <- MV.new 0xFFF
  g         <- MV.new 0
  (_2 %~ (^. errors)) <$> runStateT (inferModule <* warnTopDups) TCEnvState
    { _modBinds = modBinds'
    , _depOrder = (0 , depOrder')
    , _letBinds = letBinds'
    , _letNest  = 0
    , _errors   = emptyErrors
    , _inferStack = 0
    , _cyclicDeps = 0
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
judgeBind :: forall s. InferEnv -> Int -> IName -> IName -> TCEnv s Expr
judgeBind inferEnv letNest bindINm modBindName = use modBinds >>= \modBinds' -> let
  -- reference to inference stack (forward ref | recursive | mutual)
  preInferred :: (LetMeta , Bind) -> TCEnv s Expr
  preInferred (lm , bind) = let noop t = Core (Var (letBindIndex lm)) t
    in case bind of
    BindOK _ e  -> pure e -- pure (noop (exprType e))
    BindRenameCaptures _ _ e -> pure (noop (exprType e))
    Guard tvar -> (cyclicDeps %= (`setBit` modBindName)) $> Core (Captures (letBindIndex lm)) (tyVar tvar)
    Mutu _ _ tvar -> (cyclicDeps %= (`setBit` modBindName)) $> Core (Captures (letBindIndex lm)) (tyVar tvar)

  inferParsed :: P.FnDef -> TCEnv s Expr
  inferParsed abs = let
      modIName = eModIName inferEnv
      bindIdx = VQBindIndex (mkQName modIName modBindName)
      letMeta = LetMeta (letNest == 0) (mkQName modIName (abs ^. P.fnIName)) bindIdx (abs ^. P.fnSrc)
    in freshBiSubs 1 >>= \[tvarIdx] -> do
    inferStack %= (`setBit` modBindName) -- setup recursion/mutual guards and capture detection
    MV.write modBinds' modBindName (letMeta , Guard tvarIdx) -- recs/mutuals will biunify with our tvar
    svlc  <- letCaptures <<.= 0
    argVars <- use bruijnArgVars
    atLen <- V.length <$> use bruijnArgVars -- all capturable vars (reference where the letCaptures are valid bruijns)
    (captureRenames .=) =<< MV.new atLen

    -- run inference, need to solve scopes on top bindings (letNest 0):
    -- the infer part of (hypo infer scopeApo) can't see through LetBind vectors, so per top-bind will fuse more
    -- TODO scope can sv its params to letbinds so we can fuse anyway
    expr <- case letNest of
      0 -> hypo (inferF inferEnv) (Scope.scopeApoF (eTopBindsCount inferEnv) (eExterns inferEnv) modIName)
        (abs ^. P.fnRhs , eScopeParams inferEnv)
      _ -> cata (inferF inferEnv) (abs ^. P.fnRhs) -- let-binds were already scoped, since depend on nesting context

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
      -- TODO use mFree?
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
      <* when (is == 0) (clearBiSubs 0)

  in use bindsBitSet >>= \b -> if testBit b modBindName
    then MV.read modBinds' modBindName >>= preInferred
    else (bindsBitSet %= (`setBit` modBindName))
      *> use letBinds >>= (`MV.read` letNest) >>= \wip -> (wip `MV.read` bindINm)
      >>= inferParsed

genExpr :: IName -> LetMeta -> Term -> [Int] -> (Int , BitSet) -> Int -> TCEnv s Expr
genExpr modBindName lm term freeVarCopies (atLen , freeVars) tvarIdx = use modBinds >>= \modBinds' -> let
  rawTy = prependArrowArgsTy (tyVar <$> freeVarCopies) (tyVar tvarIdx)
  in generaliseType rawTy >>= \gTy -> let
    rawRetExpr = Core term gTy
    bind = if freeVars == 0
      then BindOK optInferred rawRetExpr
      else BindRenameCaptures atLen freeVars rawRetExpr -- Recursive binds need their free-env backpatched in
  in rawRetExpr <$ do
    use depOrder >>= \(tI , tV) -> MV.write tV tI modBindName *> (depOrder .= (tI + 1 , tV))
    MV.write modBinds' modBindName (lm , bind)

-- judgeBind > add and biunify captured arguments
getModBind :: InferEnv -> Bool -> Int -> IName -> IName -> TCEnv s Expr
getModBind inferEnv doInline letNest letName modBindName = do
  expr <- judgeBind inferEnv letNest letName modBindName
  use modBinds >>= (`MV.read` modBindName) <&> snd >>= \case
    BindOK{} -> let
      retTerm = if doInline then exprTerm expr else Var (VQBindIndex (mkQName (eModIName inferEnv) modBindName))
      in pure $ Core retTerm (exprType expr)
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
newFreeVarEnv goInEnv = do
  fl   <- use bruijnArgVars <&> V.length
  svFL <- freeLimit <<.= fl
  goInEnv <* do
    freeLimit .= svFL
    letCaptures %= (`shiftR` (fl - svFL)) -- reset relative to next enclosing let-nest

inferBlock :: InferEnv -> Int -> V.Vector P.FnDef -> Maybe (TCEnv s Expr) -> TCEnv s Expr -- , V.Vector (LetMeta , Bind))
inferBlock inferEnv liftNames letBindings inExpr = withLetNest \nest -> do
  newFreeVarEnv do
    use letBinds >>= \lvl -> V.thaw letBindings >>= MV.write lvl nest
    [0 .. V.length letBindings - 1] `forM_` \i -> judgeBind inferEnv nest i (liftNames + i)
--lets <- use modBinds >>= \v -> V.freeze (MV.slice liftNames (V.length letBindings) v) -- freeze copies it
  fromMaybe (pure poisonExpr) inExpr

retCast rc tt@(Core f ty) = case rc of { BiEQ -> tt ; c -> Core (Cast c f) ty }

inferF :: InferEnv -> P.TTF (TCEnv s Expr) -> TCEnv s Expr
inferF inferEnv = let
 withBruijnArgTVars :: Int -> TCEnv s a -> TCEnv s ([Type] , a)
 withBruijnArgTVars n go = freshBiSubs n >>= \argTVars -> do
   (bruijnArgVars %= (V.fromList argTVars <>))
   (reverse $ tyVar <$> argTVars , ) <$> go <* (bruijnArgVars %= V.drop n)

 checkFails srcOff x = use tmpFails >>= \case
   [] -> pure x
   x  -> poisonExpr <$ (tmpFails .= []) <* (errors . biFails %= (map (BiSubError srcOff) x ++))
 -- the only safe way to insert VBruijns is over terms guaranteed not to contain freevars
 -- eg: "add 3" => \papArg0 -> (\f arg1 pap0 -> f arg1 pap0) add 3 papArg0
 -- β-env will remove the innermost args while renaming VBruijns if necessary
 mkPap f args retTy pap castArgs biret = let
   argsN = length args
   papN = length pap -- TODO use argcasts
-- argTys = pap <&> (0,) -- TODO .. no inames?
   newArgs = f : castArgs args biret ++ [VBruijn i | i <- [0 .. papN - 1]]
-- newFn = BruijnAbsTyped papN (App f newArgs) argTys retTy
   newFn = let
     newArgsN = argsN + papN - 1
     bf = App (VBruijn (papN + argsN)) (VBruijn <$> [newArgsN , newArgsN - 1 .. 0])
     papFn = BruijnAbs papN mempty
     in papFn $ App (BruijnAbs (1 + papN + argsN) mempty bf) newArgs
   in d_ "making pap" $ trace (prettyTermRaw newFn) $
     Core newFn retTy
   -- ! TODO HACK must place papFn and papArgs outside lambda, else
   -- their VBruijns will be messed up
 inferApp srcOff f args = let
   castRet :: BiCast -> ([Term] -> BiCast -> [Term]) -> Expr -> Expr
   castRet biret castArgs = \case
     Core (App f args) retTy -> case biret of
       -- PAp: TODO is it always OK to eta-expand and introduce new bruijn args:
       -- papFn p1 => λx y. papFn p1 x y
       CastApp _ac (Just pap) rc -> retCast rc (mkPap f args retTy pap castArgs biret)
       CastApp _ac Nothing    rc -> retCast rc (Core (App f (castArgs args biret)) retTy)
       BiEQ -> Core (App f args) retTy
       x -> error $ show x
     t -> t
   -- TODO This will let slip some bieq casts on function arguments
   castArg (a :: Term) = \case { BiEQ -> a ; CastApp [BiEQ] Nothing BiEQ -> a ; cast -> Cast cast a }
   castArgs args' cast = case cast of
     CastApp ac _maybePap BiEQ -> zipWith castArg args' (ac ++ repeat BiEQ)
     BiEQ -> args'
     x -> error $ show x
   in if any isPoisonExpr (f : args) then pure poisonExpr else do
     (biret , retTy) <- biUnifyApp (exprType f) (exprType <$> args)
     use tmpFails >>= \case
       [] -> pure $ castRet biret castArgs (Core (App (exprTerm f) (exprTerm <$> args)) retTy)
       x  -> poisonExpr <$ (tmpFails .= []) <* (errors . biFails %= (map (BiSubError srcOff) x ++))

 judgeLabel qNameL exprs = let
   labTy = TyGround [THTyCon $ THTuple $ V.fromList (exprType <$> exprs)]
   es = exprs <&> \(Core t _ty) -> t
   in Core (Label qNameL es) (TyGround [THTyCon $ THSumTy $ BSM.singleton (qName2Key qNameL) labTy])

 -- result of mixfix solves; QVar, PExprApp
 getQBind :: VQBindIndex -> TCEnv s Expr
 getQBind qi@(VQBindIndex q) = if modName q == eModIName inferEnv -- binds at this module are at let-nest 0
   then unQName q & \i -> getModBind inferEnv False 0 i i
   else pure $ readQName (eLoadedMods inferEnv) qi & fromMaybe (error (showRawQName q))

 in \case
  P.QuestionF -> pure $ Core Question tyBot
  P.WildCardF -> pure $ Core Question tyBot
  -- letin Nothing = module / record, need to type it
  P.LetInF (P.Block _ _ lets) liftNames pInTT -> 
    inferBlock inferEnv (eTopBindsCount inferEnv + liftNames) lets (Just pInTT)
  P.ProdF pFields -> let -- duplicate the field name to both terms and types
    mkCore (ts , tys) = Core (Prod ts) (TyGround [THTyCon (THProduct tys)])
    in fmap (mkCore . BSM.unzip . BSM.fromVec)
      $ pFields `forM` \(i , s) -> s <&> \(Core t ty) -> (i , (t , ty))

  P.VParseINameF e -> error $ "panic: Unresolved IName: " <> show e
  P.VarF v -> case v of -- vars : lookup in appropriate environment
    P.VBruijn b -> use bruijnArgVars >>= \argTVars -> use freeLimit >>= \fLimit -> let
      bindArgs = V.length argTVars - fLimit -- number of args belonging to enclosing let-bind
      in (\tv -> Core (VBruijn b) (tyVar tv)) <$> if
      | b <  bindArgs -> pure (argTVars V.! b) -- local arg
      | True -> let -- if b is free, insertOrRetrieve its local tvar
        bruijnAtBind = b - bindArgs -- Bruijn idx relative to enclosing let-binding, not current lvl
        in (letCaptures <<%= (`setBit` bruijnAtBind)) >>= \oldLc -> use captureRenames >>= \cr ->
        if
         | testBit oldLc bruijnAtBind -> MV.read cr bruijnAtBind
         | True -> freshBiSubs 1 >>= \[t] -> t <$ MV.write cr bruijnAtBind t
    P.VLetBind (_iName , letNest , letIdx , i) -> getModBind inferEnv False letNest letIdx i
    P.VBruijnLevel l -> error $ "unresolve bruijnLevel: " <> show l

  P.BruijnLamF (P.BruijnAbsF argCount argMetas _nest rhs) ->
    withBruijnArgTVars argCount rhs <&> \(argTVars , Core term retTy) -> if argCount == 0 then Core term retTy else
      let fnTy = prependArrowArgsTy argTVars retTy
          alignArgs :: These (IName, Int) Type -> (Int, Type)
          alignArgs = these ((,tyBot) . fst) ((-1,)) (\(i , _) b -> (i , b)) -- TODO argMetas should match argCount
      in  Core (BruijnAbsTyped argCount term (alignWith alignArgs argMetas argTVars) retTy) fnTy

  P.AppF src fTT argsTT  -> fTT  >>= \f -> sequence argsTT >>= inferApp src f
  P.PExprAppF src _prec q argsTT -> getQBind (VQBindIndex q) {-TODO push into pexprapp-} >>= \f -> sequence argsTT >>= inferApp src f
  P.RawExprF t -> t
  P.MixfixPoisonF t -> poisonExpr <$ (tmpFails .= []) <* (errors . mixfixFails %= (t:))
  P.MFExprF srcOff m -> let err = MixfixError srcOff ("Lone mixfix word: " <> show m)
    in poisonExpr <$ (tmpFails .= []) <* (errors . mixfixFails %= (err:))
  P.IQVarF q -> getQBind q

  P.TupleIdxF qN tt -> tt >>= \(Core tuple tupleTy) -> freshBiSubs 1 >>= \[i] -> let
    expectedTy = TyGround [THTyCon $ THProduct (BSM.singleton qN (tyVar i))]
    in bisub tupleTy expectedTy <&> \cast ->
      let obj = TTLens tuple [qN] LensGet in Core (case cast of { BiEQ -> obj ; cast -> Cast cast obj }) (tyVar i)
  P.TTLensF o tt fieldsLocal maybeSet -> tt >>= \record -> let
    fields = qName2Key . mkQName (eModIName inferEnv) <$> fieldsLocal
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
               -- TODO clean casts
               CastProduct _drops bsm | [(asmIdx , _cast)] <- BSM.toList bsm -> Cast (CastOver asmIdx ac fn outT) object
               BiEQ -> object
               _ -> error $ "expected CastProduct: " <> show rc

         pure $ Core lensOverCast (mergeTVar rT (mkExpected outT))

  -- TODO when to force introduce local label vs check if imported
  P.LabelF localL tts -> sequence tts <&> judgeLabel (mkQName (eModIName inferEnv) localL)
  P.QLabelF q -> {-sequence tts <&>-} pure (judgeLabel q [])
 -- sumTy = THSumTy (BSM.singleton (qName2Key q) (TyGround [THTyCon $ THTuple mempty]))

  P.DataF alts -> do
    tys <- sequence (alts <&> \(l , params) -> ({-qName2Key (mkQName (moduleIName) l)-} l ,) <$> sequence params)
    alts <- tys `forM` \(lI , params) -> (params `forM` exprToTy) <&> \altTy ->
      (qName2Key (mkQName (eModIName inferEnv) lI) , tHeadToTy $ THTyCon (THTuple (V.fromList altTy)))
    pure $ Core (Ty (tHeadToTy $ THTyCon (THSumTy (BSM.fromList alts)))) (tySet 0) -- max of universe in alts

  -- TODO gadt must have a signature for the whole thing also!
--P.GadtF alts -> do
--  sumArgsMap <- alts `forM` \(l , tyParams , _gadtSig@Nothing) -> do
--    params <- tyParams `forM` \t -> t
--    pure (l , TyGround [THTyCon $ THTuple $ V.fromList params])
--  pure $ Core (Ty (TyGround [THTyCon $ THSumTy $ BSM.fromListWith mkLabelCol sumArgsMap])) (TySet 0)

  -- Convert a declared label to a function TODO this is not pretty, should improve collecting labels from a data decl
  P.LabelDeclF l iNm -> getModBind inferEnv True 0 0 iNm <&> \(Core term _ty) -> case term of
    Ty (TyGround [THTyCon (THSumTy ts)]) | qL <- mkQName (eModIName inferEnv) l
      , Just labTy@(TyGround [THTyCon (THTuple paramTys)]) <- ts BSM.!? qName2Key qL -> let
        labelTy = if V.null paramTys then labTy else tHeadToTy (THTyCon (THArrow (V.toList paramTys) labTy))
        in Core (Label qL []) labelTy
    -- v eg. Maybe a = ..
--  BruijnAbsTyped n (Ty fn) -> _
    x -> error $ show x

  P.MatchBF mkScrut caseSplits catchAll -> mkScrut >>= \(Core scrut gotScrutTy) -> do
    altExprs <- caseSplits `forM` \(pat , mkRhs) -> do
      Core rhs rawRhsTy <- mkRhs
      let rhsTy = case rhs of { BruijnAbsTyped _ _ _ rT -> rT ; _ -> rawRhsTy }
          altFnTy = case rhs of
            BruijnAbsTyped _ _t ars _retT -> tHeadToTy (THTyCon $ THTuple (V.fromList $ snd <$> ars))
            _ -> tHeadToTy (THTyCon (THTuple mempty))
      (l , patTy) <- case pat of -- Either
        -- | use the type the rhs function expects
        Right l -> pure (l , altFnTy)
        -- | use the sumtype declaration
        Left  (l , iNm) -> getModBind inferEnv True 0 0 iNm >>= \(Core term _ty) -> case term of
          Ty (TyGround [THTyCon (THSumTy ts)])
            -- vv Biunify the rhs function and the expected label type
            | qL <- qName2Key l , Just t <- ts BSM.!? qL -> (qL , t) <$ bisub t altFnTy
          x -> error $ show x
      pure ((l , (rhs , patTy)) , rhsTy)
    def <- sequenceA catchAll
    let rhsTys = snd <$> (altExprs :: [((Int , (Term , Type)) , Type)])
        altScrutTys = BSM.fromList $ altExprs <&> \((q , (_term , ty)) , _rhsTy) -> (q , ty)
        retTy   = mergeTypeList False $ maybe rhsTys ((: rhsTys) . exprType) def -- ? TODO why negative merge
        scrutTy = TyGround [THTyCon if isJust def then THSumOpen altScrutTys else THSumTy altScrutTys]
        altTerms = BSM.fromList $ altExprs <&> \((q , (term , _ty)) , rhsTy) -> (q , (term , rhsTy))
    (b , matchTy) <- biUnifyApp (TyGround (mkTyArrow [scrutTy] retTy)) [gotScrutTy]
    case b of { BiEQ -> pure () ; CastApp [BiEQ] Nothing BiEQ -> pure () ; c -> error $ "expected bieq; " <> show c }
--  pure $ Core (CaseB scrut scrutTy alts (exprTerm <$> def)) matchTy
    pure $ Core (mergeCaseBranches retTy scrut matchTy altTerms def) matchTy

  P.TypedF t ty -> t >>= \(Core term gotT) -> do
    genGotTy <- generaliseType gotT
    annTy    <- ty >>= exprToTy
    Core term <$> checkAnnotation genGotTy annTy
  P.InlineExprF e -> pure e
  P.LitF l        -> pure $ Core (Lit l) (TyGround [THPrim (typeOfLit l)])
  P.PLitArrayF ls -> pure $ Core (Lit (LitArray ls)) (TyGround [THTyCon $ THArray $ mergeTypeHeadList True (THPrim . typeOfLit <$> ls)])
  P.PArrayF ls    -> sequence ls <&> \exprs -> unzipExprs exprs & \(elems , tys) ->
    Core (Array (V.fromList elems)) (TyGround [THTyCon $ THArray $ mergeTypeList True tys])
  P.ScopePoisonF e   -> poisonExpr <$ (tmpFails .= []) <* (errors . scopeFails %= (e:))
  P.DesugarPoisonF t -> poisonExpr <$ (tmpFails .= []) <* (errors . unpatternFails %= (t:))
  P.ScopeWarnF w t   -> (errors . scopeWarnings %= (w:)) *> t
  P.ForeignF{} {- isVA i tt-} -> error "not ready for foreign"
--  tt <&> \(Core _ttExpr ty) -> Core (Var (VForeign i)) ty
  x -> error $ "not implemented: inference of: " <> show (embed $ P.WildCard <$ x)
