{-# Language TemplateHaskell #-}
module FEnv where
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

debug_fuse = False

-- The only optimisation worth doing is fusing Match with Labels
-- All cases "eventually" receive structure; fusion blocks on args | recursion
-- Most of the complexity here addresses fusion accross fn (partial) applications
-- Thus we un-inline cases and branches to allow partial inlining (upto structure)

-- ? static arg transformation vs partial specialisation

-- specialisations are keyed on arg structure (labels | constants)
data ArgShape
 = ShapeNone
 | ShapeLabel ILabel [ArgShape]
 | ShapeQBind QName
 deriving (Ord , Eq , Show)

getArgShape ∷ Term → ArgShape
getArgShape = \case
  Label l params → ShapeLabel l (getArgShape <$> params)
  Var (VQBind q) → ShapeQBind q
  _ → ShapeNone

data FEnv s = FEnv
 { _thisMod     ∷ IName
 , _cBinds      ∷ MV.MVector s Bind
 , _self        ∷ IName
 , _structure   ∷ [CaseID] -- passed down to indicate we're building a fusable
 , _argTable    ∷ MV.MVector s Term
 , _useArgTable ∷ Bool   -- toggle to beta-reduce or not
 , _activeBetas ∷ BitSet
 , _specStack   ∷ BitSet -- ensure not to inline a spec into itself
 , _bindStack   ∷ BitSet

 , _specCache   ∷ MV.MVector s (M.Map [ArgShape] IName) -- Bind → Spec cache
 -- v INamed fresh specialisations: -- Nothing marks recursive specs, ie. noinline
 , _specBound   ∷ MV.MVector s (Maybe Term)
 , _specsLen    ∷ Int
 , _bruijnArgs  ∷ Maybe (V.Vector Term) -- fresh argNames for specialisations

 -- name and extract all cases and branches (to cheapen duplication and inlining)
 , _branches    ∷ MV.MVector s Term -- always Abs
 , _cases       ∷ MV.MVector s (BSM.BitSetMap ABS , Maybe ABS) -- BranchIDs
 , _caseLen     ∷ CaseID
 , _branchLen   ∷ BranchID
 }; makeLenses ''FEnv
type SimplifierEnv s = StateT (FEnv s) (ST s)

stackFn betaReducable go = do
  aT ← use argTable
  sv ← betaReducable `forM` \i → ((i,) <$> MV.read aT i) <* MV.write aT i (Var (VArg i))
  go <* (sv `forM_` \(i , arg) → MV.write aT i arg)

addCase newCase = do
  n  ← caseLen <<%= (1+)
  s  ← use cases ≫= \cs → (cases <.=) =≪ if MV.length cs <= n then MV.grow cs 32 else pure cs
  n <$ MV.write s n newCase

addBranch newBranch = do
  n  ← branchLen <<%= (1+)
  s  ← use branches ≫= \br → (branches <.=) =≪ if MV.length br <= n then MV.grow br 32 else pure br
  n <$ MV.write s n newBranch

addSpec ∷ Int → Int → Term → SimplifierEnv s ()
addSpec s bruijnN term = do
  sb    ← use specBound
  specs ← (specBound <.=) =≪ if MV.length sb <= s
    then MV.grow sb 32 ≫= \v → v <$ ([s..s+31] `forM_` \i → MV.write v i Nothing)
    else pure sb
  MV.write specs s (Just (if bruijnN == 0 then term else BruijnAbs bruijnN 0 term))

destructureArgs ∷ [Term] → (Int , [Term] , [Term] , [ArgShape])
destructureArgs args = let
  (ret , bruijnN) = traverse solveArg args `runState` 0
  (  unstructuredArgsL -- subExpressions of Labels , now deBruijn args
   , repackedArgsL     -- original args with label subExprs replaced with deBruijn args
   , argShapes)
   = unzip3 ret
  solveArg ∷ Term → State Int ([Term] , [Term] , ArgShape)
  solveArg arg = case arg of
    Var (VQBind q) → pure ([] , [arg] , ShapeQBind q)
    Label l ars → traverse solveArg ars <&> \case
      [] → ([] , [Label l []] , ShapeLabel l []) -- lone label is like a constant VQBind
      (a : ars) → let
        go (u,r,s) (u',r',s') = (u ++ u' , [Label l (r ++ r')] , ShapeLabel l [s' , s])
        in foldl go a ars
    rawArg         → gets identity ≫= \bruijn → modify (1+) $> ([rawArg] , [VBruijn bruijn] , ShapeNone)
  in (bruijnN , concat unstructuredArgsL , concat repackedArgsL , argShapes)

-- Replace all label | const args with new deBruijn argNames
-- q is (either spec to respecialise or bind to specialise)
data MkSpec = ReSpec QName | SpecBind QName
mkSpec ∷ MkSpec → Term → [Term] → SimplifierEnv s (Maybe Term)
mkSpec q body args = let
  (bruijnN , unstructuredArgs , repackedArgs , argShapes) = destructureArgs args
  rawSpec = App body repackedArgs -- Simplifying this will produce our specialisation as λBruijn → body'
  bindName = case q of { ReSpec q → modName q ; SpecBind q → unQName q }
  dontSpec = all (\case { ShapeNone → True ; _ → False }) argShapes -- TODO return shapes?
  in if dontSpec then pure Nothing else Just <$> do
  s ← specsLen <<%= (1+) -- reserve a slot (this spec may be recursive)
  use specCache ≫= \sc → MV.modify sc (M.insert argShapes s) bindName -- immediately register it for recursive specs

  when debug_fuse $ traceM $ "raw spec " <> show s <> "\n" <> show argShapes <> "\n" <> prettyTermRaw rawSpec
  spec ← simpleTerm rawSpec
  when debug_fuse $ traceM $ "simple spec " <> show s <> "\n" <> prettyTermRaw spec <> "\n"
  addSpec s bruijnN spec

  let specName = mkQName bindName s -- bindName . Spec number
  case s of -- TODO inline iff we're under some cases!
--  s → inlineSpec specName ≫= \case -- HACK
--    Label l p → pure (Label l (p ++ unstructuredArgs))
--    spec      → simpleApp spec unstructuredArgs
    _ → pure $ if null unstructuredArgs then Spec specName
               else App (Spec specName) unstructuredArgs

-- should always inline when non-recursive
-- TODO this should depend on wrappingCases
inlineSpec q = let unQ = unQName q in use specStack ≫= \ss → if ss `testBit` unQ then pure (Spec q)
  else use specBound ≫= \sb → MV.read sb unQ ≫= \case
    Nothing → pure (Spec q)
    Just t  → (specStack %= (`setBit` unQ)) $> t -- if b == 0 then t else BruijnAbs b 0 t

-- Inline partially a binding if we believe something will fuse
inlineMaybe ∷ QName → wrapCases → [Term] → SimplifierEnv s Term
inlineMaybe q cs args = use thisMod ≫= \mod → let
  bindINm  = unQName q
  noInline = App (Var (VQBind q)) args
  (_bruijnN , unstructuredArgs , _repackedArgs , argShapes) = destructureArgs args
  in do
  -- try a cached specialisation of this bind
  use specCache ≫= \sc → MV.read sc bindINm <&> (M.!? argShapes) ≫= \case
    Just sName → use specBound ≫= \sb → MV.read sb sName ≫= let
      -- since we're applying a spec, need to unwrap the args
      in d_ (argShapes , sName) $ \case
      -- v Recursion guard (don't stack specialising same arg shapes)
      Nothing → pure $ App (Spec (mkQName bindINm sName)) unstructuredArgs
      Just s  → simpleApp s unstructuredArgs
    Nothing → if mod /= modName q
      then pure noInline
      else simpleBind bindINm ≫= \case -- make a specialisation
        BindOK _o _l _r (Core inlineF _ty) | shouldSpec _ args cs
          -- If recursive, we must spawn a specialisation.
          -- Also may as well cache non-recursive specs rather than alwaysinline
          → fromMaybe noInline <$> mkSpec (SpecBind q) inlineF args
        _ → pure noInline

forceInline q = simpleBind (unQName q) <&> \case
  BindOK _o _l _r (Core inlineF _ty) → Just inlineF
  _ → Nothing

-- Is this worth inlining
-- | Does fn Case any of its args
-- | Does fn produce any Labels
shouldSpec _fnInfo _args _caseWraps = True
  -- unfused cases have a dependency tree: (ScrutApp | ScrutArg) ⇒ each case: [Args] required to reduce
  -- * inline only happens upto cases/branches

simplifyBindings ∷ IName → Int → Int → MV.MVector s Bind → ST s (FEnv s)
simplifyBindings modIName nArgs nBinds bindsV = do
  argSubs ← MV.new nArgs
  br      ← MV.new 32
  cs      ← MV.new 32
  sc      ← MV.replicate nBinds mempty -- ? should we save specs in their bindings
  sb      ← MV.replicate 5 Nothing -- TODO test grow with small values here
  ((simpleBind `mapM` [0 .. nBinds - 1]) *> traceSpecs nBinds) `execStateT` FEnv
    { _thisMod     = modIName
    , _cBinds      = bindsV
    , _self        = -1
    , _structure   = []
    , _argTable    = argSubs
    , _useArgTable = False
    , _activeBetas = emptyBitSet

    , _specStack   = emptyBitSet
    , _bindStack   = emptyBitSet

    , _specCache   = sc -- a Map of ArgShapes → Spec for each bind
    , _specBound   = sb -- raw binds table
    , _specsLen    = 0
    , _bruijnArgs  = mempty

    , _branches    = br
    , _cases       = cs
    , _caseLen     = 0
    , _branchLen   = 0
    }

traceSpecs ∷ Int → SimplifierEnv s ()
traceSpecs nBinds = do
  sb ← use specBound
  sl ← use specsLen
  traceM "-- Specs --"
  [0..sl-1] `forM_` \i → MV.read sb i ≫= \case
    Just t → traceM ("spec " <> show i <> " = " <> prettyTermRaw t)
    Nothing      → pure ()
  sc ← use specCache
  [0..nBinds-1] `forM_` \i → MV.read sc i ≫= \m → if M.null m then pure () else traceM $ "π" <> show i <> " specs " <> show m

-- read from bindList, simplify or return binding and guard recursion
simpleBind ∷ Int → SimplifierEnv s Bind
simpleBind bindN = use cBinds ≫= \cb → MV.read cb bindN ≫= \b → do
  bindStack %= (`setBit` bindN)
  MV.write cb bindN Queued
  newB ← newBetaEnv $ case b of
    BindOK n l isRec (Core t ty) → if n /= 0 then pure b else simpleTerm t <&> \case
      -- catch top level partial application (ie. extra implicit args)
      App (Instr (MkPAp _n)) (f2 : args2) → let
        (arTs , retT) = getArrowArgs ty
        in BindOK n l isRec $ Core (PartialApp arTs f2 args2) retT
      newT → BindOK n l isRec $ Core newT ty
    _x → pure {-$ trace ("not bindok: " <> show bindN <> " " <> show x ∷ Text)-} Queued
  newB <$ MV.write cb bindN newB

-- newBinds must not re-use wip β-reduction env from a previous bind in the stack
newBetaEnv go = (activeBetas <<.= emptyBitSet) ≫= \svBetas → go <* (activeBetas .= svBetas)

inBetaEnv ∷ [(Int , Type)] → BitSet → [Term] → SimplifierEnv s Term → SimplifierEnv s ([(Int , Type)] , [Term] , Term)
inBetaEnv argDefs _free args go = let
  (resArgDefs , trailingArgs , betaReducable) = partitionThese (align argDefs args)
  in do
  svUseAt ← useArgTable <<.= True
  aT ← use argTable
  sv ← betaReducable `forM` \((i,_ty) , arg) → ((i,) <$> MV.read aT i) <* MV.write aT i arg
  svB ← activeBetas <<%= (.|. intList2BitSet (fst . fst <$> betaReducable))
  r ← go <&> \case
    Abs (_lam , t) → t -- rm the abs wrapper (para can't do it preemptively)
    x → x
  useArgTable .= svUseAt
  activeBetas .= svB
  sv `forM_` \(i , arg) → MV.write aT i arg
  pure (resArgDefs , trailingArgs , r)

bruijnEnv ∷ Int → BitSet → [Term] → SimplifierEnv s Term → SimplifierEnv s Term
bruijnEnv n _free args go = do
--traceM $ "BRUIJN" <> show n <> " " <> prettyTermRaw t <> "  $$$  " <> foldr (<>) "" (map prettyTermRaw args)
  svBruijn ← bruijnArgs <<.= Just (V.fromList args)
  when (isJust svBruijn) $ error "stacking bruijn β-reduction"
  when (n /= length args) (error "bruijnPap")
  r ← go <&> \case
    BruijnAbs _ _ t → t
    x → x
  (bruijnArgs .= svBruijn)
  pure r

-- Note. if we beta-reduce an arg with some fn of itself (while deriving specialisations)
-- must not β-reduce it again: ie. Excessive calls to simpleTerm are incorrect. para helps guarantee this
simpleTerm ∷ Term → SimplifierEnv s Term
simpleTerm = RS.para go where
  go ∷ TermF (Term , SimplifierEnv s Term) -> SimplifierEnv s Term
  go = \case
    VBruijnF v → use bruijnArgs <&> maybe (VBruijn v) (V.! v)
    VarF v → case v of
      VArg i   → use activeBetas ≫= \betas → if betas `testBit` i then use argTable ≫= \at → MV.read at i
        else pure (Var (VArg i))-- ≫= \a → a <$ traceM (show i <> " β " <>  prettyTermRaw a)
      VQBind i → pure (Var (VQBind i))
      v        → pure (Var v) -- ext | foreign
    SpecF q     → inlineSpec q
    AppF f args → case fst f of
      -- paramorphism catches Abs so we can setup β-reduction env before running f
      -- ! This assumes simpleTerm never changes argDefs
      Abs ((Lam argDefs free _ty , _body)) → traverse snd args ≫= \ars → inBetaEnv argDefs free ars (snd f) <&> \([],[],r) → r
      BruijnAbs n free _t → traverse snd args ≫= \ars → bruijnEnv n free ars (snd f)
      _     → snd f ≫= \rawF → traverse snd args ≫= simpleApp rawF
    MatchF scrut retT branches d → snd scrut ≫= \sc
      → fuseMatch retT sc (map snd <$> branches) (map snd <$> d)
    -- Don't leak β-envs
    t → embed <$> sequence (fmap snd t)

-- one-step fusion on images of recursion
simpleApp ∷ Term → [Term] → SimplifierEnv s Term
simpleApp f sArgs = let noop = App f sArgs in case f of
  Instr i        → pure (simpleInstr i sArgs)
  Label l params → pure (Label l (params ++ sArgs))
  App f1 args1   → simpleApp f1 (args1 ++ sArgs) -- can try again
--Lens
--Case caseId scrut   → error $ show caseId
  Abs _                 → error "uncaught Abs-App"
  BruijnAbs _n _free _t → error "uncaught BruijnAbs-App"
  opaqueFn → use structure ≫= \case
    [] → pure noop
    -- If we're building a scrutinee, partial inline upto the fusable structure
    cs → case opaqueFn of
--    Match{}        → pure noop
      Var (VArg _)   → pure noop
      VBruijn _      → pure noop
      Spec _         → pure noop -- inlineSpecMaybe?
      Var (VQBind q) → inlineMaybe q cs sArgs -- partial inline if produces / consumes labels
      x → error (toS (prettyTermRaw x) <> "\n" <> (concatMap ((++ "\n") . toS . prettyTermRaw) sArgs))
--    Case caseID scrut → use cases ≫= \c → MV.read c caseID ≫= \(br , d) → fuseMatch _ (pure scrut) br d

-- Crucially we fuse first to then simplify only the relevant branches in the new fused β-env
fuseMatch ∷ Type → Term → BitSetMap (Lam, (SimplifierEnv s Term)) → Maybe (Lam, (SimplifierEnv s Term)) → SimplifierEnv s Term
fuseMatch retT scrut branches d = case scrut of
  -- trivial case-of-label Delay simplifying case-alts until we setup β-env:
  Label l params → let
    Just (Lam argDefs free _ty , body) = (branches BSM.!? qName2Key l) <|> d
    in inBetaEnv argDefs free params body <&> \(_resArgDefs@[] , _trailingArgs@[] , ret) → ret

  -- case-of-case: push outer case into each branch,
  -- then the inner case fuses with outer case output labels
  Match innerScrut ty2 innerBranches innerDefault → let
    pushCase (Lam ars free ty , innerBody) = 
      (Lam ars free ty , fuseMatch ty innerBody branches d)
    optBranches = pushCase <$> innerBranches
    optD        = pushCase <$> innerDefault
    in fuseMatch ty2 innerScrut optBranches optD

  Spec q → inlineSpec q ≫= \s → fuseMatch retT s branches d

  Var (VQBind q) → forceInline q ≫= \case
    Just scrutInline → fuseMatch retT scrutInline branches d
    Nothing → error "failed to inline" -- pure noop

  -- opaque scrut = App | Arg ; ask scrut to be inlined up to Label;
  -- This will require specialising | inlining enclosing function
  -- un-inline the case
  _opaque → do
    br ← sequence $ fmap sequence branches
    dd ← sequence $ fmap sequence d
    caseID ← addCase (br , dd)
    structure %= (caseID :)
--  pure (Case caseID opaque)
    pure $ Match scrut retT br dd
