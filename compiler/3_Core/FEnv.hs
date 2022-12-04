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

debug_fuse = True

-- The only optimisation worth doing is fusing Match with Labels
-- All cases "eventually" receive structure; fusion blocks on args | recursion
-- Most of the complexity here addresses fusion accross fn (partial) applications
-- Thus we un-inline cases and branches to allow partial inlining (upto structure)

-- ? static arg transformation vs partial specialisation

-- specialisations are keyed on arg structure (labels | constants)
data FEnv s = FEnv
 { _thisMod     ∷ IName
 , _cBinds      ∷ MV.MVector s Bind
 , _structure   ∷ [CaseID] -- passed down to indicate we're building a fusable
 , _argTable    ∷ MV.MVector s Term
 , _activeBetas ∷ BitSet
 , _specStack   ∷ BitSet -- ensure not to inline a spec into itself
-- , _bindStack   ∷ BitSet

 , _specCache   ∷ MV.MVector s (M.Map [ArgShape] IName) -- Bind -> Spec cache
 -- v INamed fresh specialisations: -- Nothing marks recursive specs, ie. noinline
 , _specBound   ∷ MV.MVector s (Maybe (FnSize , Term))
 , _specsLen    ∷ Int
 , _bruijnArgs  ∷ Maybe (V.Vector Term) -- fresh argNames for specialisations

 -- name and extract all cases and branches (to cheapen duplication and inlining)
-- , _branches    ∷ MV.MVector s Term -- always Abs
-- , _branchLen   ∷ BranchID
-- , _cases       ∷ MV.MVector s (BSM.BitSetMap LamB , Maybe LamB) -- BranchIDs
-- , _caseLen     ∷ CaseID
 }; makeLenses ''FEnv
type SimplifierEnv s = StateT (FEnv s) (ST s)

--stackFn betaReducable go = do
--  aT <- use argTable
--  sv <- betaReducable `forM` \i -> ((i,) <$> MV.read aT i) <* MV.write aT i (Var (VArg i))
--  go <* (sv `forM_` \(i , arg) -> MV.write aT i arg)

--addCase newCase = do
--  n  <- caseLen <<%= (1+)
--  s  <- use cases>>= \cs -> (cases <.=) =≪ if MV.length cs <= n then MV.grow cs 32 else pure cs
--  n <$ MV.write s n newCase

--addBranch newBranch = do
--  n  <- branchLen <<%= (1+)
--  s  <- use branches >>= \br -> (branches <.=) =≪ if MV.length br <= n then MV.grow br 32 else pure br
--  n <$ MV.write s n newBranch

addSpec ∷ Int -> Int -> Term -> SimplifierEnv s FnSize
addSpec s bruijnN term = do
  sb    <- use specBound
  specs <- (specBound <.=) =≪ if MV.length sb <= s
    then MV.grow sb 32 >>= \v -> v <$ ([s..s+31] `forM_` \i -> MV.write v i Nothing)
    else pure sb
  let etaReduced = if bruijnN == 0 then term else case term of
        -- η-reduce bruijns: eg. \Bruijn 2 ⇒ f B0 B1 rewrites to f
        App f args | and $ Prelude.imap (\i arg -> case arg of { (VBruijn x) -> x == i ; _ -> False }) args -> f
--      App (BruijnAbs 1 _free (Match (VBruijn 0) t branches d)) [scrut] -> Match scrut t branches d
        _ -> BruijnAbs bruijnN 0 term
      -- check if fn is larger than 1 apps, otherwise can inline it for free - the State monad allows this to shortcut
      fnSize ∷ Int
      fnSize = cata go etaReduced `evalState` 0 where
        go = \case
          AppF f ars -> get >>= \n -> if n > 2 then pure n else modify (1+) *> ((\f ars -> f + sum ars) <$> f <*> sequence ars)
          _ -> pure 0
      smallFn = fnSize <= 1
  smallFn <$ MV.write specs s (Just (smallFn , etaReduced))

destructureArgs ∷ [Term] -> (Int , [Term] , [Term] , [ArgShape])
destructureArgs args = let
  (ret , bruijnN) = traverse solveArg args `runState` 0
  (  unstructuredArgsL -- subExpressions of Labels , now deBruijn args
   , repackedArgsL     -- original args with label subExprs replaced with deBruijn args
   , argShapes)
   = unzip3 ret
  solveArg ∷ Term -> State Int ([Term] , [Term] , ArgShape)
  solveArg arg = case arg of
    Var (VQBind q) -> pure ([] , [arg] , ShapeQBind q)
    Label l ars -> traverse solveArg ars <&> \case
      [] -> ([] , [Label l []] , ShapeLabel l []) -- lone label is like a constant VQBind
      ars -> unzip3 ars & \(uL , rL , shL) -> (concat uL , [Label l (concat rL)] , ShapeLabel l shL)
    rawArg         -> gets identity >>= \bruijn -> modify (1+) $> ([rawArg] , [VBruijn bruijn] , ShapeNone)
  in (bruijnN , concat unstructuredArgsL , concat repackedArgsL , argShapes)

-- Replace all label | const args with new deBruijn argNames
-- q is (either spec to respecialise or bind to specialise)
data MkSpec = ReSpec QName | SpecBind QName
mkSpec ∷ MkSpec -> Term -> [Term] -> SimplifierEnv s (Maybe Term)
mkSpec q body args = let
  (bruijnN , unstructuredArgs , repackedArgs , argShapes) = destructureArgs args
  rawSpec = App body repackedArgs -- Simplifying this will produce our specialisation as λBruijn -> body'
  bindName = case q of { ReSpec q -> modName q ; SpecBind q -> unQName q }
  dontSpec = all (\case { ShapeNone -> True ; _ -> False }) argShapes -- TODO return shapes?
  in if dontSpec then pure Nothing else Just <$> do
  s <- specsLen <<%= (1+) -- reserve a slot (this spec may be recursive)
  use specCache >>= \sc -> MV.modify sc (M.insert argShapes s) bindName -- immediately register it for recursive specs

  when debug_fuse $ traceM $ "raw spec " <> show s <> "\n" <> show argShapes <> "\n" <> prettyTermRaw rawSpec
  spec <- simpleTerm rawSpec
  when debug_fuse $ traceM $ "simple spec " <> show s <> "\n" <> prettyTermRaw spec <> "\n"
  small <- addSpec s bruijnN spec

  let specName = mkQName bindName s -- bindName . Spec number
  if small -- TODO also inline iff we're under some cases!
  then inlineSpecApp specName unstructuredArgs
  else pure $ if null unstructuredArgs then Spec specName
              else App (Spec specName) unstructuredArgs

-- should always inline when non-recursive
-- TODO this should depend on wrappingCases
inlineSpec q = let unQ = unQName q in use specStack >>= \ss -> if ss `testBit` unQ then pure (Spec q)
  else use specBound >>= \sb -> MV.read sb unQ >>= \case
    Nothing -> pure (Spec q)
    Just (_fnSz , t) -> (specStack %= (`setBit` unQ)) $> t

inlineSpecApp specName args = inlineSpec specName >>= \case
  f@BruijnAbs{} -> simpleTerm (App f args) -- have to re-simplify the body with new args (β-optimality?)
  f -> simpleApp f args

-- Inline partially a binding if we believe something will fuse
inlineMaybe :: Bool -> QName -> wrapCases -> [Term] -> SimplifierEnv s Term
inlineMaybe True _ _ _ = error "how to inline / update let-bound specs?"
inlineMaybe False q cs args = use thisMod >>= \mod -> let
  bindINm  = unQName q
  noInline = App (Var (VQBind q)) args
  (_bruijnN , unstructuredArgs , _repackedArgs , argShapes) = destructureArgs args
  in do
  -- try a cached specialisation of this bind
  use specCache >>= \sc -> MV.read sc bindINm <&> (M.!? argShapes) >>= \case
    Just sName -> use specBound >>= \sb -> MV.read sb sName >>= let
      -- since we're applying a spec, need to unwrap the args
      in {-d_ (argShapes , sName) $-} \case
      -- v Recursion guard (don't stack specialising same arg shapes)
      Nothing -> pure $ App (Spec (mkQName bindINm sName)) unstructuredArgs
      Just (_ , s) -> simpleApp s unstructuredArgs
    Nothing -> if mod /= modName q
      then pure noInline
      else simpleLetName bindINm >>= \case -- make a specialisation
        BindOK _o _l _r (Core inlineF _ty) | shouldSpec _ args cs
          -- If recursive, we must spawn a specialisation.
          -- Also may as well cache non-recursive specs rather than alwaysinline
          -> fromMaybe noInline <$> mkSpec (SpecBind q) inlineF args
        _ -> pure noInline

forceInline ∷ QName -> SimplifierEnv s (Maybe Term)
forceInline q = simpleLetName (unQName q) <&> \case -- make a specialisation
  BindOK _o _l _r (Core inlineF _ty) -> Just inlineF
  _ -> Nothing

-- Is this worth inlining
-- | Does fn Case any of its args
-- | Does fn produce any Labels
shouldSpec _fnInfo _args _caseWraps = True
  -- unfused cases have a dependency tree: (ScrutApp | ScrutArg) ⇒ each case: [Args] required to reduce
  -- * inline only happens upto cases/branches

--simplifyBindings ∷ IName -> MV.MVector s Bind -> ST s (Maybe Specialisations)
simplifyModule ∷ IName -> Expr -> ST s (Expr , Maybe Specialisations)
simplifyModule modIName mod = do
  argSubs <- MV.new 0
--br      <- MV.new 32
--cs      <- MV.new 32
  sc      <- MV.replicate 0{-nbinds-} mempty -- ? should we save specs in their bindings
  sb      <- MV.replicate 5 Nothing -- TODO test grow with small values here
  cBinds' <- MV.new 0
--s <- ((simpleLetName `mapM_` [0 .. nBinds - 1]) *> traceSpecs nBinds) `execStateT` FEnv
  (retTT , s) <- simpleExpr mod `runStateT` FEnv
    { _thisMod     = modIName
    , _cBinds      = cBinds'
    , _structure   = []
    , _argTable    = argSubs
    , _activeBetas = emptyBitSet

    , _specStack   = emptyBitSet
--  , _bindStack   = emptyBitSet

    , _specCache   = sc -- a Map of ArgShapes -> Spec for each bind
    , _specBound   = sb -- raw binds table
    , _specsLen    = 0
    , _bruijnArgs  = mempty

--  , _cases       = cs
--  , _caseLen     = 0
 -- , _branches    = br
 -- , _branchLen   = 0
    }
  let slen = s._specsLen
  sb' <- map (fromMaybe $ error "no specialisation?") . V.take slen <$> V.unsafeFreeze s._specBound
  sc' <- V.unsafeFreeze s._specCache
  pure $ if slen == 0 then (retTT , Nothing) else (retTT , Just (Specialisations sb' sc'))

--traceSpecs ∷ Int -> SimplifierEnv s ()
traceSpecs nBinds = do
  sl <- use specsLen
  when (sl /= 0) $ do
    sb <- use specBound
    traceM "-- Specs --"
    [0..sl-1] `forM_` \i -> MV.read sb i >>= \case
      Just (_ , t) -> traceM ("spec " <> show i <> " = " <> prettyTermRaw t)
      Nothing      -> pure ()
    sc <- use specCache
    [0..nBinds-1] `forM_` \i -> MV.read sc i >>= \m -> if M.null m then pure () else traceM $ "π" <> show i <> " specs " <> show m

-- read from bindList, simplify or return binding and guard recursion
simpleLetName :: Int -> SimplifierEnv s Bind
simpleLetName bindN = use cBinds >>= \cb -> MV.read cb bindN >>= \b -> do
--bindStack %= (`setBit` bindN)
  MV.write cb bindN WIP
  newB <- simpleBind b
  newB <$ MV.write cb bindN newB

simpleBind :: Bind -> SimplifierEnv s Bind
simpleBind b = newBetaEnv $ case b of
  BindOK n l isRec (Core t ty) -> if n /= 0 then pure b else simpleTerm t <&> \case
    -- catch top level partial application (ie. extra implicit args)
    App (Instr (MkPAp _n)) (f2 : args2) -> let
      (arTs , retT) = getArrowArgs ty
      in BindOK n l isRec $ Core (_PartialApp arTs f2 args2) retT
    newT -> BindOK n l isRec $ Core newT ty
  _x -> pure {-$ trace ("not bindok: " <> show bindN <> " " <> show x ∷ Text)-} WIP

simpleExpr :: Expr -> SimplifierEnv s Expr
simpleExpr (Core t ty) = simpleTerm t <&> \t' -> Core t' ty -- ?! how tf did this work when t was typoed instead of t'
simpleExpr PoisonExpr = pure PoisonExpr
simpleExpr x = pure $ d_ x PoisonExpr

-- newBinds must not re-use wip β-reduction env from a previous bind in the stack
newBetaEnv go = (activeBetas <<.= emptyBitSet) >>= \svBetas -> (bruijnArgs <<.= Nothing) >>= \svBruijn ->
  go <* (activeBetas .= svBetas) <* (bruijnArgs .= svBruijn)

-- Should be able to rm
inBetaEnv ∷ [(Int , Type)] -> BitSet -> [Term] -> SimplifierEnv s Term -> SimplifierEnv s ([(Int , Type)] , [Term] , Term)
inBetaEnv argDefs _free args go = let
  (resArgDefs , trailingArgs , betaReducable) = partitionThese (align argDefs args)
  in do
  aT <- use argTable
  sv <- betaReducable `forM` \((i,_ty) , arg) -> ((i,) <$> MV.read aT i) <* MV.write aT i arg
  svB <- activeBetas <<%= (.|. intList2BitSet (fst . fst <$> betaReducable))
  r <- go <&> \case
--  Abs (_lam , t) -> t -- rm the abs wrapper (para can't do it preemptively)
    x -> x
  activeBetas .= svB
  sv `forM_` \(i , arg) -> MV.write aT i arg
  pure (resArgDefs , trailingArgs , r)

bruijnEnv ∷ Int -> BitSet -> [Term] -> SimplifierEnv s Term -> SimplifierEnv s Term
bruijnEnv n _free args go = do
  when (n /= length args) (error "bruijnPap")
  let unBruijnAbs = \case
        BruijnAbs _ _ t -> t
        x -> x
      newEnv args go = (bruijnArgs <<.= Just (V.fromList args)) >>= \svBruijn -> go <* (bruijnArgs .= svBruijn)
  use bruijnArgs >>= \case
    -- stacked bruijns: β-reduce the args in the new β-env (the body cannot reference the new bruijn args)
    Just _  -> (simpleTerm `mapM` args) *> newEnv args (go <&> unBruijnAbs)
    Nothing -> newEnv args $ go <&> unBruijnAbs

-- Note. if we β-reduce an arg with some fn of itself (while deriving specialisations)
-- must not β-reduce it again: ie. Excessive calls to simpleTerm are incorrect. para helps guarantee this
simpleTerm ∷ Term -> SimplifierEnv s Term
simpleTerm = RS.para go where
  go :: TermF (Term , SimplifierEnv s Term) -> SimplifierEnv s Term
  go = \case
    LetBlockF lets -> LetBlock <$> lets `forM` \(lm , bind) -> (lm ,) <$> simpleBind bind
    LetBindsF lets inE -> LetBinds
      <$> (lets `forM` \(lm , bind) -> (lm ,) <$> simpleBind bind)
      <*> simpleTerm (fst inE)
    VBruijnF v -> use bruijnArgs <&> maybe (VBruijn v) (V.! v)
    VarF v -> case v of
--    VArg i   -> use activeBetas >>= \betas -> if betas `testBit` i then use argTable >>= \at -> MV.read at i
--      else pure (Var (VArg i))-- >>= \a -> a <$ traceM (show i <> " β " <>  prettyTermRaw a)
      VQBind i   -> pure (Var (VQBind i))
      VLetBind q -> pure (Var (VLetBind q)) -- TODO should inline?
      v          -> pure (Var v) -- ext | foreign
--  SpecF q     -> inlineSpec q
    AppF f args -> case fst f of
      -- paramorphism catches Abs so we can setup β-reduction env before running f
      -- ! This assumes simpleTerm never changes argDefs
      BruijnAbs n free _t -> traverse snd args >>= \ars -> bruijnEnv n free ars (snd f)
      Spec q -> traverse snd args >>= inlineSpecApp q
      _      -> snd f >>= \rawF -> traverse snd args >>= simpleApp rawF
    CaseBF scrut retT branches d -> snd scrut >>= \sc -> fuseMatch retT sc (map snd <$> branches) (map snd <$> d)
    -- Don't leak β-envs
    t -> embed <$> sequence (fmap snd t)

-- one-step fusion on images of recursion
simpleApp ∷ Term -> [Term] -> SimplifierEnv s Term
simpleApp f sArgs = let noop = App f sArgs in case f of
  Instr i        -> pure (simpleInstr i sArgs)
  Label l params -> pure (Label l (params ++ sArgs))
  App f1 args1   -> simpleApp f1 (args1 ++ sArgs) -- can try again
--Lens
--Case caseId scrut   -> error $ show caseId
--BruijnAbs 1 _free (Match (VBruijn 0) t branches d) | [scrut] <- sArgs -> pure $ Match scrut t branches d
  -- TODO which fusion step let this slip
  BruijnAbs n free t   -> bruijnEnv n free sArgs (simpleTerm t) -- TODO avoid this random resimplification !
--BruijnAbs _n _free t -> error $ "uncaught BruijnAbs-App: " <> show t
  opaqueFn -> use structure >>= \case
    [] -> pure noop
    cs -> case opaqueFn of -- If building a scrut, partial inline upto the fusable structure
      VBruijn _        -> pure noop
      Spec _           -> pure noop -- inlineSpecMaybe?
      Var (VQBind q)   -> inlineMaybe False q cs sArgs -- partial inline if produces / consumes labels
      Var (VLetBind q) -> inlineMaybe True  q cs sArgs -- partial inline if produces / consumes labels
      x -> error (toS (prettyTermRaw x) <> "\n" <> (concatMap ((++ "\n") . toS . prettyTermRaw) sArgs))

-- Crucially fuse first to then simplify only the relevant branches in the new fused β-env
fuseMatch :: Type -> Term -> BitSetMap (Lam, (SimplifierEnv s Term)) -> Maybe (Lam, (SimplifierEnv s Term))
  -> SimplifierEnv s Term
fuseMatch retT scrut branches d = case scrut of
  -- trivial case-of-label Delay simplifying case-alts until we setup β-env:
  Label l params -> let Just (Lam argDefs free _ty , body) = (branches BSM.!? qName2Key l) <|> d
    in inBetaEnv argDefs free params body <&> \([] , [] , ret) -> ret

  -- case-of-case: push outer case into each branch,
  -- then the inner case fuses with outer case output labels
  CaseB innerScrut ty2 innerBranches innerDefault -> let
    pushCase (Lam ars free ty , innerBody) =
      (Lam ars free ty , fuseMatch ty innerBody branches d)
--  pushCase innerBody = fuseMatch (TyGround []) innerBody branches d -- TODO type?
    optBranches = pushCase <$> innerBranches
    optD        = pushCase <$> innerDefault
    in fuseMatch ty2 innerScrut optBranches optD

  Spec q -> inlineSpec q >>= \s -> fuseMatch retT s branches d

  Var (VQBind q) -> forceInline q >>= \case
    Just scrutInline -> fuseMatch retT scrutInline branches d
    Nothing -> error "failed to inline" -- pure noop

  App (Var (VQBind q)) args -> forceInline q >>= \case
    Just f  -> simpleTerm (App f args) >>= \scrut2 -> fuseMatch retT scrut2 branches d
    Nothing -> error "failed to inline"
--App (b@BruijnAbs{}) args ->  error $ show b

  -- opaque scrut = App | Arg ; ask scrut to be inlined up to Label;
  -- This will require specialising | inlining enclosing function
  -- un-inline the case
  _opaque -> do
--  traceM $ "opaque: " <> (prettyTermRaw opaque)
    br <- traverse sequence branches -- traverse sequence
    dd <- traverse sequence d
--  caseID <- addCase (br , dd)
    structure %= (0 :) -- TODO
--  pure (Case caseID opaque)
    pure (CaseB scrut retT br dd)
