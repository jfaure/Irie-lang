{-# Language TemplateHaskell #-}
module FEnv (simplifyModule) where
import CoreSyn
import SimplifyInstr
import Prim
import PrettyCore
import CoreUtils
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.Map as M
import BitSetMap as BSM
import Data.Functor.Foldable as RS
import Control.Lens
import Data.List (unzip3)
-- TODO identify ReCons => rewrite to Lens operations
-- make Dup nodes

normalise = True
debug_fuse = True

-- The only optimisation worth doing is fusing Match with Labels
-- All cases "eventually" receive structure; fusion blocks on args | recursion
-- Most of the complexity here addresses fusion accross fn (partial) applications
-- Thus we un-inline cases and branches to allow partial inlining (up to structure)

-- ? static arg transformation vs partial specialisation

-- ? Spawning new specialisations for imported bindings
-- ? Lift all lambdas | make Bruijn names (let-bounds may escape their scope !)
-- ? lifting Bruijns outside their binder: eg. by returning them
-- * Perhaps can rename case-branches to account for freeVar / linearity difference
-- * Inline maybe
-- "All stream combinators must be inlined and specialised"
-- * Specialise on partial application of free function
-- TODO partial application of letName applied to more args failed

-- ↓ β-env setup @ App (Lam) _ars
-- ↑ one-step fusion ; β-reduction & inlining ; λ lifting

-- specialisations are keyed on arg structure (labels | constants)
data FEnv s = FEnv
 { _thisMod    :: IName
 , _cBinds     :: MV.MVector s Bind
 , _structure  :: [CaseID] -- passed down to indicate we're building a fusable

 , _bruijnArgs :: V.Vector Term -- fresh argNames for specialisations

 , _letBinds   :: MV.MVector s (MV.MVector s Bind)
 , _letNest    :: Int
 , _interpret  :: Bool -- inline, β-reduce and constant-fold everything

 -- name and extract all cases and branches (to cheapen duplication and inlining)
-- , _branches    :: MV.MVector s Term -- always Abs
-- , _branchLen   :: BranchID
-- , _cases       :: MV.MVector s (BSM.BitSetMap LamB , Maybe LamB) -- BranchIDs
-- , _caseLen     :: CaseID
 }; makeLenses ''FEnv
type SimplifierEnv s = StateT (FEnv s) (ST s)

termSize :: Term -> Int -- TODO perhaps still avoid inlining large records / tycons
termSize term = cata go term `evalState` 0 where
  go = \case
    AppF f ars -> get >>= \n -> if n > 2 then pure n else modify (1+) *> ((\f ars -> f + sum ars) <$> f <*> sequence ars)
    _ -> pure 0

--addCase newCase = do
--  n  <- caseLen <<%= (1+)
--  s  <- use cases>>= \cs -> (cases <.=) =≪ if MV.length cs <= n then MV.grow cs 32 else pure cs
--  n <$ MV.write s n newCase

--addBranch newBranch = do
--  n  <- branchLen <<%= (1+)
--  s  <- use branches >>= \br -> (branches <.=) =≪ if MV.length br <= n then MV.grow br 32 else pure br
--  n <$ MV.write s n newBranch

-- !? does this assign VBruijns in reverse
destructureArgs :: [Term] -> (Int , [Term] , [Term] , [ArgShape])
destructureArgs args = let
  (ret , bruijnN) = traverse solveArg args `runState` 0
  (  unstructuredArgsL -- subExpressions of Labels , now deBruijn args
   , repackedArgsL     -- original args with label subExprs replaced with deBruijn args
   , argShapes)
   = unzip3 ret
  solveArg :: Term -> State Int ([Term] , [Term] , ArgShape)
  solveArg arg = case arg of
    Var (VQBind q)   -> pure ([] , [arg] , ShapeQBind q)
    Var (VLetBind q) -> pure ([] , [arg] , ShapeLetBind q)
    -- avoid specialising on builtins, which can never fuse
    App (Var (VLetBind q)) ars -> traverse solveArg ars <&> \ars ->
      unzip3 ars & \(uL , rL , shL) -> (concat uL , [App (Var (VLetBind q)) (concat rL)] , ShapePAPLet q shL)
    Label l ars -> traverse solveArg ars <&> \case
      [] -> ([] , [Label l []] , ShapeLabel l []) -- lone label is like a constant VQBind
      ars -> unzip3 ars & \(uL , rL , shL) -> (concat uL , [Label l (concat rL)] , ShapeLabel l shL)
    rawArg         -> gets identity >>= \bruijn -> modify (1+) $> ([rawArg] , [VBruijn bruijn] , ShapeNone)
  in (bruijnN , reverse $ concat unstructuredArgsL , concat repackedArgsL , argShapes)

-- TODO HACK letbinds may escape their scope !!
getLetSpec q argShapes = d_ ("warning: not robust if the let-bound escapes its scope") $ 
  use letBinds >>= \lb -> (lb `MV.read` modName q) >>= \bindVec -> MV.read bindVec (unQName q) <&> \case
    BindOK o expr@(Core inlineF _ty) -> fromMaybe (error "no bind-spec !") (bindSpecs o M.!? argShapes)

-- Inline partially an App or its specialisation if expect something to fuse
-- fully inline unconditionally if interpreting
-- True = letbind ; false = VQBind
specApp :: Bool -> QName -> wrapCases -> [Term] -> SimplifierEnv s Term
specApp isLetBind q cs args = use thisMod >>= \mod -> case isLetBind of
--True  -> pure (App (Var (VLetBind q)) args)
  True  -> let
    nest = modName q ; bindNm  = unQName q
    noInline = App (Var (VLetBind q)) args
    x@(bruijnN , unstructuredArgs , repackedArgs , argShapes) = destructureArgs args
    in {-d_ args $ d_ repackedArgs $ d_ unstructuredArgs $ -}
    use letBinds >>= \lb -> (lb `MV.read` nest) >>= \bindVec -> MV.read bindVec bindNm >>= \case
    BindOK o expr@(Core inlineF _ty) -> case {-d_ (q , argShapes) $-} bindSpecs o M.!? argShapes of
      Just cachedSpec -> simpleTerm $ App cachedSpec $ unstructuredArgs
      Nothing -> if all (\case { ShapeNone -> True ; _ -> False }) argShapes then pure noInline else do
        let recGuard = LetSpec q argShapes
        MV.modify bindVec (\(BindOK (OptBind oLvl oSpecs) t)
          -> BindOK (OptBind oLvl (M.insert argShapes recGuard oSpecs)) expr) bindNm

        -- fully simplify the specialised partial application (if it recurses then the spec is extremely valuable)
        let raw = App inlineF repackedArgs
            rawAbs = if bruijnN == 0 then raw else BruijnAbs bruijnN emptyBitSet raw

        spec <- identityBruijn bruijnN -- We're working under a fresh bruijn wrapper
          $ simpleApp inlineF repackedArgs
        let specFn = if bruijnN == 0 then spec else BruijnAbs bruijnN emptyBitSet spec -- HACK
--      when debug_fuse $ traceM $ show args <> "\n" <> show repackedArgs <> "\n" <> show unstructuredArgs
        when debug_fuse $ traceM $ "raw spec "    <> prettyTermRaw raw <> "\n"
        when debug_fuse $ traceM $ "simple spec " <> prettyTermRaw specFn <> "\n"

        MV.modify bindVec (\(BindOK (OptBind oLvl oSpecs) t)
          -> BindOK (OptBind oLvl (M.insert argShapes specFn oSpecs)) expr) bindNm

        -- TODO inline spec iff under some cases || fully β-reducing || small
        -- Need to deep simplify to ensure VBruijn consistency if any present in unstructuredArgs
        if null unstructuredArgs then simpleTerm specFn else simpleTerm $ App specFn unstructuredArgs
    _ -> pure noInline

  -- Don't specialise imported binds
  False -> let noInline = App (Var (VQBind q)) args in pure noInline

forceInline :: QName -> SimplifierEnv s (Maybe Term)
forceInline q = simpleLetName (unQName q) <&> \case -- make a specialisation
  BindOK _o (Core inlineF _ty) -> Just inlineF
  _ -> Nothing

forceInlineLetBind q = let letDepth = modName q ; bindNm = unQName q
  in use letBinds >>= \lb -> (lb `MV.read` letDepth) >>= \b -> MV.read b bindNm <&> \case
    BindOK _o (Core inlineF _ty) -> Just inlineF
    _ -> Nothing

-- Is this worth inlining
-- | Does fn Case any of its args
-- | Does fn produce any Labels
shouldSpec _fnInfo _args _caseWraps = True
  -- unfused cases have a dependency tree: (ScrutApp | ScrutArg) ⇒ each case: [Args] required to reduce
  -- * inline only happens upto cases/branches

--simplifyBindings :: IName -> MV.MVector s Bind -> ST s (Maybe Specialisations)
simplifyModule :: IName -> Expr -> ST s (Expr , Maybe Specialisations)
simplifyModule modIName mod = do
--br       <- MV.new 32
--cs       <- MV.new 32
  cBinds'  <- MV.new 0
  letBinds' <- MV.new 16
  (retTT , s) <- simpleExpr mod `runStateT` FEnv
    { _thisMod     = modIName
    , _cBinds      = cBinds'
    , _structure   = []

    , _bruijnArgs  = mempty

    , _interpret   = False
    , _letBinds    = letBinds'
    , _letNest     = 0

--  , _cases       = cs , _caseLen     = 0
--  , _branches    = br , _branchLen   = 0
    }
  pure $ (retTT , Nothing)

-- read from bindList, simplify or return binding and guard recursion
simpleLetName :: Int -> SimplifierEnv s Bind
simpleLetName bindN = use cBinds >>= \cb -> MV.read cb bindN >>= \b -> do
  MV.write cb bindN WIP
  newB <- simpleBind b
  newB <$ MV.write cb bindN newB

simpleBind :: Bind -> SimplifierEnv s Bind
simpleBind b = case b of
  BindOK (OptBind optlvl specs) (Core t ty) -> if optlvl /= 0 then pure b else simpleTerm t <&> \case
    newT -> BindOK (OptBind (optlvl + 1) specs) $ Core newT ty
  _x -> pure {-$ trace ("not bindok: " <> show bindN <> " " <> show x :: Text)-} WIP

simpleExpr :: Expr -> SimplifierEnv s Expr
simpleExpr (Core t ty) = simpleTerm t <&> \t' -> Core t' ty -- ?! how tf did this work when t was typoed instead of t'
simpleExpr PoisonExpr = pure PoisonExpr
simpleExpr x = pure $ d_ x PoisonExpr

-------------------
-- Bruijn β-envs --
-------------------
readVBruijn v = use bruijnArgs <&> \vec -> if v < V.length vec
  then let r = vec V.! v in {-d_ (v , r , vec)-} r
  else {-error $ show $-} VBruijn (v + 100) -- ie. bug probably

incBruijns n args = do
  sv <- use bruijnArgs
  bruijnArgs .= V.generate (V.length sv) (\i -> VBruijn (i + n))
  ret <- mapM simpleTerm args
  bruijnArgs .= sv
  pure ret

identityBruijn n go = (bruijnArgs <<%= (V.generate n VBruijn <>)) >>= \sv -> go <* (bruijnArgs .= sv)

-- Enter bruijn abstraction
bruijnEnv :: Int -> BitSet -> SimplifierEnv s Term -> SimplifierEnv s Term
bruijnEnv n 0 go = go -- do
--prevSubs <- use bruijnArgs
--fixSubs  <- pure prevSubs -- incBruijns n prevSubs
--bruijnArgs .= (new <> fixSubs)
--go <* (bruijnArgs .= prevSubs)

-- Application under a bruijn abstraction => override bruijn subs + clear resulting abstraction
bruijnApp :: Int -> BitSet -> [Term] -> SimplifierEnv s Term -> SimplifierEnv s Term
bruijnApp n 0 args go | n /= 0 && n == length args = do
  prev <- use bruijnArgs
  incBruijns n prev >>= \prev' -> bruijnArgs .= (V.reverse (V.fromList args) <> prev')
--prev <- bruijnArgs <<%= \prev -> V.reverse (V.fromList args) <> prev
  r <- go <* (bruijnArgs .= prev) <&> \case
    BruijnAbs m _ t          | m == n -> t
    BruijnAbsTyped m _ t _ _ | m == n -> t
    x -> x
  when debug_fuse $ traceM $ "App: "  <> prettyTermRaw (App Question args) <> "\n"
  when debug_fuse $ traceM $ prettyTermRaw r <> "\n"
  pure r

bruijnApp n free args go = error $ "Bruijn-pap: " <> show (n , length args , args)

--incTermBruijns n = cata $ \case
--  VBruijnF x -> VBruijn (x + n)
--  MatchBF{} -> error "LamB obscures term from cata"
--  t -> embed t

-- Note. if we β-reduce an arg with some fn of itself (while deriving specialisations)
-- must not β-reduce it again: ie. Excessive calls to simpleTerm are incorrect. para helps guarantee this
simpleTerm :: Term -> SimplifierEnv s Term
simpleTerm = RS.para go where
  -- Add local let-binds to env
  inferBlock lets go = do
    traceM "incBlock"
    nest <- letNest <<%= (1+)
    use letBinds >>= \lvl -> V.thaw (snd <$> lets) >>= MV.write lvl nest
    r <- go
    traceM "decBlock"
    letNest %= \x -> x - 1
    pure r
  go :: TermF (Term , SimplifierEnv s Term) -> SimplifierEnv s Term
  go term = case term of -- d_ (embed $ Question <$ term) $ case term of
    LetBlockF lets -> inferBlock lets $ LetBlock <$> lets `forM` \(lm , bind) -> (lm ,) <$> simpleBind bind
    LetBindsF lets inE -> inferBlock lets $ do
      newLets <- lets `forM` \(lm , bind) -> (lm ,) <$> simpleBind bind
      newInE  <- simpleTerm (fst inE)
      pure (LetBinds newLets newInE)
    VBruijnF v -> readVBruijn v
    VarF v -> pure $ case v of
      VQBind i   -> Var v
      VLetBind q -> Var v -- TODO should inline?
      VForeign{} -> Var v -- ext | foreign
--  SpecF q     -> inlineSpec q
    BruijnAbsF n free body          -> BruijnAbs n free <$> bruijnEnv n free (snd body)
    BruijnAbsTypedF n free body _ _ -> BruijnAbs n free <$> bruijnEnv n free (snd body)
    AppF f args -> case fst f of
      -- paramorphism catches Abs so we can setup β-reduction env before running f
      BruijnAbs n free t          -> traverse snd args >>= \ars -> bruijnApp n free ars (snd f)
      BruijnAbsTyped n free t _ _ -> traverse snd args >>= \ars -> bruijnApp n free ars (snd f)
--    Spec q -> traverse snd args >>= inlineSpecApp q
--    VBruijn i -> App (VBruijn i) <$> traverse snd args
--    x -> error $ show x
      _      -> snd f >>= \rawF -> traverse snd args >>= simpleApp rawF
    CaseBF scrut retT branches d -> snd scrut >>= \sc -> fuseMatch retT sc (map snd <$> branches) (map snd <$> d)
    MatchBF{} -> error ""
    -- Don't leak β-envs
    t -> embed <$> sequence (fmap snd t)

-- one-step fusion on images of recursion
simpleApp :: Term -> [Term] -> SimplifierEnv s Term
simpleApp f sArgs = let noop = App f sArgs in case f of
  Instr i        -> pure $ if normalise then simpleInstr i sArgs else App (Instr i) sArgs
  Label l params -> pure (Label l (params ++ sArgs))
  App f1 args1   -> simpleApp f1 (args1 ++ sArgs) -- can try again
--Lens
--Case caseId scrut   -> error $ show caseId
  -- TODO which fusion step let this slip
  -- TODO avoid this random resimplification !
  BruijnAbs n free t   -> bruijnApp n free sArgs (simpleTerm f)
  BruijnAbsTyped n free t _argTs _retT -> bruijnApp n free sArgs (simpleTerm f)
--BruijnAbs _n _free t -> error $ "uncaught BruijnAbs-App: " <> show t -- Should be eliminated at Inference
--BruijnAbsTyped _n _free t _ _ -> error $ "uncaught BruijnAbsTyped-App: " <> show t
  opaqueFn -> use structure >>= \case
    [] -> pure noop
    cs -> case opaqueFn of -- If building a scrut, partial inline upto the fusable structure
      VBruijn _        -> pure noop
      Var (VQBind q)   -> specApp False q cs sArgs -- partial inline if produces / consumes labels
      Var (VLetBind q) -> specApp True  q cs sArgs -- partial inline if produces / consumes labels
      LetSpec q shp    -> getLetSpec q shp >>= \f -> pure $ App f sArgs -- simpleApp f sArgs
      x -> error (toS (prettyTermRaw x) <> "\n" <> (concatMap ((++ "\n") . toS . prettyTermRaw) sArgs))

-- Fuse first to only simplify the relevant branch in the new fused β-env
fuseMatch :: Type -> Term -> BitSetMap (LamBEnv , (SimplifierEnv s Term)) -> Maybe (LamBEnv , (SimplifierEnv s Term))
  -> SimplifierEnv s Term
fuseMatch retT scrut branches d = case scrut of
  -- trivial case-of-label Delay simplifying case-alts until we setup β-env:
  Label l params -> case (branches BSM.!? qName2Key l) <|> d of
    Just (LamBEnv n argDefs retT , body) -> if n == 0 
      then (if null params then body else error $ show params)
      else bruijnApp n 0 params body
    Nothing -> error $ "panic: label not found: " <> show l <> " : " <> show params <> "\n; " <> show (BSM.keys branches)

  -- case-of-case: push outer case into each branch,
  -- then the inner case fuses with outer case output labels
  CaseB innerScrut ty2 innerBranches innerDefault -> let
    pushCase (LamBEnv n argDefs retT , innerBody) =
      (LamBEnv n argDefs retT , fuseMatch retT innerBody branches d)
    optBranches = pushCase <$> innerBranches
    optD        = pushCase <$> innerDefault
    in fuseMatch ty2 innerScrut optBranches optD

  LetSpec q sh -> error $ show q --Spec q -> inlineSpec q >>= \s -> fuseMatch retT s branches d

  Var (VQBind q) -> forceInline q >>= \case
    Just scrutInline -> fuseMatch retT scrutInline branches d
    Nothing -> error "failed to inline" -- pure noop
  Var (VLetBind q) -> forceInlineLetBind q >>= \case
    Just scrutInline -> fuseMatch retT scrutInline branches d
    Nothing -> error "failed to inline" -- pure noop

  -- Should force subexpressions upto structure if possible (ie. f is VBruijn or app is non-specialisable)
  App f@(BruijnAbs{})      args -> simpleApp f args >>= \scrut2 -> fuseMatch retT scrut2 branches d
  App f@(BruijnAbsTyped{}) args -> simpleApp f args >>= \scrut2 -> fuseMatch retT scrut2 branches d

  -- opaque scrut = App | Arg ; ask scrut to be inlined up to Label;
  -- This will require specialising | inlining enclosing function
  -- un-inline the case
  opaque -> do
    traceM $ "opaque: " <> (prettyTermRaw opaque)
    br <- traverse sequence branches -- traverse sequence
    dd <- traverse sequence d
--  caseID <- addCase (br , dd)
    structure %= (0 :) -- TODO
--  pure (Case caseID opaque)
    pure (CaseB scrut retT br dd)
