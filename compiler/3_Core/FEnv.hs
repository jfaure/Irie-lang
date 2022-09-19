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

debug_fuse = True

-- The only optimisation worth doing is fusing Match with Labels
-- Most of the complexity here addresses fusion accross fn (partial) applications

-- * mk standalone fn for case + case-splits
-- * record arg shapes
-- ? conditional destructuring

-- ? static arg transformation vs partial specialisation
-- All cases "eventually" receive structure; fusion blocks on args | recursion

-- key specialisations on arg structure + constants
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
 , _structure   ∷ [CaseID] -- passed down to indicate fusable expected
 , _argTable    ∷ MV.MVector s Term
 , _useArgTable ∷ Bool -- toggle to beta-reduce or not
 , _specStack   ∷ BitSet -- ensure not to inline a spec into itself
 , _bindStack   ∷ BitSet

 , _specCache   ∷ MV.MVector s (M.Map [ArgShape] IName) -- Bind → Spec cache
 -- v INamed fresh specialisations: (bruijnN , body) -- Nothing marks recursive specs, ie. noinline
 , _specBound   ∷ MV.MVector s (Maybe (Int , Term))
 , _specsLen    ∷ Int
 , _bruijnArgs  ∷ Maybe (V.Vector Term) -- fresh argNames for specialisations

 -- name and extract all cases and branches (to cheapen duplication and inlining)
 , _branches    ∷ MV.MVector s Term -- always Abs
 , _cases       ∷ MV.MVector s (BSM.BitSetMap ABS , Maybe ABS) -- BranchIDs
 , _caseLen     ∷ CaseID
 , _branchLen   ∷ BranchID
 }; makeLenses ''FEnv
type SimplifierEnv s = StateT (FEnv s) (ST s)

addCase newCase = do
  n  ← caseLen <<%= (1+)
  cs ← use cases
  s  ← (cases <.=) =≪ (if MV.length cs <= n then MV.grow cs 32 else pure cs)
  n <$ MV.write s n newCase

addBranch newBranch = do
  n  ← branchLen <<%= (1+)
  br ← use branches 
  s  ← (branches <.=) =≪ if MV.length br <= n then MV.grow br 32 else pure br
  n <$ MV.write s n newBranch

addSpec ∷ Int → Int → Term → SimplifierEnv s ()
addSpec s bruijnN term = do
  sb    ← use specBound
  specs ← (specBound <.=) =≪ if MV.length sb <= s
    then MV.grow sb 32 ≫= \v → v <$ ([s..s+31] `forM_` \i → MV.write v i Nothing)
    else pure sb
  MV.write specs s (Just (bruijnN , term))

-- Replace all label | const args with new deBruijn argNames
-- q is (either spec to respecialise or bind to specialise)
data MkSpec = ReSpec QName | SpecBind QName
mkSpec ∷ MkSpec → Term → [Term] → SimplifierEnv s (Maybe Term)
mkSpec q body args = let
  (ret , bruijnN) = traverse solveArg args `runState` 0
  (  unstructuredArgsL -- subExpressions of Labels , now deBruijn args
   , repackedArgs      -- original args with label subExprs replaced with deBruijn args
   , argShapes)
   = unzip3 ret
  unstructuredArgs = concat unstructuredArgsL
  solveArg ∷ Term → State Int ([Term] , [Term] , ArgShape)
  solveArg arg = case arg of
    Var (VQBind q) → pure ([] , [arg] , ShapeQBind q)
    Label l ars → traverse solveArg ars <&> \case
      [] → ([] , [Label l []] , ShapeLabel l []) -- lone label is like a constant VQBind
      (a : ars) → let
        go (u,r,s) (u',r',s') = (u ++ u' , [Label l (r ++ r')] , ShapeLabel l [s' , s])
        in foldl go a ars
    rawArg         → gets identity ≫= \bruijn → modify (1+) $> ([rawArg] , [VBruijn bruijn] , ShapeNone)
  rawSpec = App body (concat repackedArgs)
  bindName = case q of { ReSpec q → modName q ; SpecBind q → unQName q }
  dontSpec = all (\case { ShapeNone → True ; _ → False }) argShapes -- TODO return shapes?
  in if dontSpec then pure Nothing else Just <$> do
  s ← specsLen <<%= (1+) -- reserve a slot (this spec may be recursive)
  use specCache ≫= \sc → MV.modify sc (M.insert argShapes s) bindName -- immediately register it for recursive specs
  when debug_fuse $ traceM $ "raw spec " <> show s <> "\n" <> prettyTermRaw rawSpec
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
    Just (b , t) → (specStack %= (`setBit` unQ)) $> if b == 0 then t else BruijnAbs b 0 t

-- Inline partially a binding if we believe something will fuse
inlineMaybe ∷ QName → wrapCases → [Term] → SimplifierEnv s Term
inlineMaybe q cs args = use thisMod ≫= \mod → let
  bindINm = unQName q
  noInline = App (Var (VQBind q)) args
  in do
  -- search for a cached specialisation of this bind
  use specCache ≫= \sc → MV.read sc bindINm <&> (M.!? (getArgShape <$> args)) ≫= \case
    Just sName → use specBound ≫= \sb → (fmap snd <$> MV.read sb sName) ≫= \case
      Nothing → pure $ case noInline of -- ? Are we first-time simplifying the spec
        -- TODO if applying a spec, need to unwrap the args !
        _ → App (Spec (mkQName bindINm sName)) args -- noInline -- Recursion guard (don't stack specialising recursive fns)
--      _ → noInline -- first time simplifying the spec, don't replace with itself
--    Just s  → pure $ App s args -- simpleApp s args
      Just s  → simpleApp s args
    Nothing → {-use bindStack ≫= \bindstack →-} if mod /= modName q -- || bindstack `testBit` bindINm
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
  argSubs ← MV.generate nArgs (Var . VArg)
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
    Just (_ , t) → traceM ("spec " <> show i <> " = " <> prettyTermRaw t)
    Nothing      → pure ()
  sc ← use specCache
  [0..nBinds-1] `forM_` \i → MV.read sc i ≫= \m → if M.null m then pure () else traceM $ "π" <> show i <> " specs " <> show m

-- read from bindList, simplify or return binding and guard recursion
simpleBind ∷ Int → SimplifierEnv s Bind
simpleBind bindN = use cBinds ≫= \cb → MV.read cb bindN ≫= \b → do
  bindStack %= (`setBit` bindN)
  MV.write cb bindN Queued
  newB ← case b of
    BindOK n l isRec (Core t ty) → if n /= 0 then pure b else simpleTerm t <&> \case
      -- catch top level partial application (ie. extra implicit args)
      App (Instr (MkPAp _n)) (f2 : args2) → let
        (arTs , retT) = getArrowArgs ty
        in BindOK n l isRec $ Core (PartialApp arTs f2 args2) retT
      newT → BindOK n l isRec $ Core newT ty
    _x → pure {-$ trace ("not bindok: " <> show bindN <> " " <> show x ∷ Text)-} Queued
  newB <$ MV.write cb bindN newB

-- Note. if we beta-reduce an arg with some fn of itself (while deriving specialisations)
-- must not β-reduce it again: ie. Excessive calls to simpleTerm are incorrect
-- para helps clarify the recursion, each step gives (pre-image , image) of the recursion
simpleTerm ∷ Term → SimplifierEnv s Term
simpleTerm = RS.para $ \case
  VBruijnF v → use bruijnArgs <&> maybe (VBruijn v) (V.! v)
  VarF v → case v of
    VArg i   → use argTable ≫= \at → MV.read at i -- ≫= \a → a <$ traceM (show i <> " β " <>  prettyTermRaw a) 
    VQBind i → pure (Var (VQBind i))
    v        → pure (Var v) -- ext | foreign
  SpecF q     → inlineSpec q
  AppF f args → case fst f of
    -- paramorphism catches Abs so we can setup β-reduction env before running f
    -- ! This assumes simpleTerm never changes argDefs
    Abs ((Lam argDefs free _ty , _body)) → traverse snd args ≫= \ars → inBetaEnv argDefs free ars (snd f) <&> \(_,_,r) → r
    BruijnAbs n _free _t → error $ show n
    _     → snd f ≫= \rawF → traverse snd args ≫= simpleApp rawF
  RecAppF f args → case fst f of
    Abs ((Lam argDefs free _ty , _body)) → traverse snd args ≫= \ars → inBetaEnv argDefs free ars (snd f) <&> \(_,_,r) → r
    BruijnAbs n _free _t → error $ show n
    _     → snd f ≫= \rawF → traverse snd args ≫= simpleApp rawF
  t → embed <$> sequence (fmap snd t)

inBetaEnv ∷ [(Int , Type)] → BitSet → [Term] → SimplifierEnv s Term → SimplifierEnv s ([(Int , Type)] , [Term] , Term)
inBetaEnv argDefs _free args go = let
  (resArgDefs , trailingArgs , betaReducable) = partitionThese (align argDefs args)
  in do
  svUseAt ← useArgTable <<.= True
  aT ← use argTable
  sv ← betaReducable `forM` \((i,_ty) , arg) → ((i,) <$> MV.read aT i) <* MV.write aT i arg
  r ← go <&> \case
    Abs (_lam , t) → t -- rm the abs wrapper (para can't do it preemptively)
    x → x
  useArgTable .= svUseAt
  sv `forM_` \(i , arg) → MV.write aT i arg
  pure (resArgDefs , trailingArgs , r)

-- Perform β-reduction on an Abs. Have to simplify the body (again)
-- Note. if some arg is substituted with a fn of itself (while deriving specialisations),
-- do not β-reduce it there: Excessive calls to simpleTerm are incorrect
foldAbs ∷ ABS → [Term] → SimplifierEnv s Term
foldAbs (Lam argDefs free _ty , body) args = do
--traceM $ "---------" <> show argDefs <> " " <> prettyTermRaw body <> "  $$$  " <> foldr (<>) "" (map prettyTermRaw args)
  (resArgDefs , trailingArgs , bodyOpt) ← inBetaEnv argDefs free args (simpleTerm body)
  when (not (null resArgDefs)) (traceM $ "resArgDefs! " <> show resArgDefs)
  case trailingArgs of
    []  → pure bodyOpt
    ars → simpleApp bodyOpt ars

-- one-step fusion
simpleApp ∷ Term → [Term] → SimplifierEnv s Term
simpleApp f sArgs = let noop = App f sArgs in case f of
  Instr i      → pure (simpleInstr i sArgs)
  -- v this is slightly dubious if the inner App returns a function (eg. Match)
--App (Match{}) _ → pure noop -- cannot tack args onto a Match
--App f2 args2 → simpleApp f2 (trace (show f2 <> "\n$$ " <> show args2 <> "\n$$$$ " <> show sArgs ∷ Text) $ args2 ++ sArgs) -- can try again
  App f1 args1   → simpleApp f1 (args1 ++ sArgs) -- can try again
  Label l params → pure $ Label l (params ++ sArgs)

  -- app-abs uncaught by para (was inlined) ⇒ need to resimplify body, which is why case&branch extraction is important
--Abs (Lam argDefs free ty , body) → foldAbs argDefs free body ty sArgs
  Abs _ → error "" -- foldAbs argDefs free body ty sArgs
  BruijnAbs n _free t → do
    svBruijn ← bruijnArgs <<.= Just (V.fromList sArgs)
    when (isJust svBruijn) $ error "stacking bruijn β-reduction"
    when (n /= length sArgs) (error "bruijnPap")
    simpleTerm t <* (bruijnArgs .= svBruijn)

--Lens
--Case caseId scrut → error $ show caseId
  Match retT branches d → case sArgs of
    []             → error "impossible empty match"
    [scrut]        → fuseMatch retT scrut branches d
    (scrut : args) → (`App` args) <$> fuseMatch retT scrut branches d
  opaqueFn → use structure ≫= \case
    [] → pure noop
    -- If we're building a scrutinee, partial inline upto the fusable structure
    cs → case opaqueFn of
      Var (VArg _)   → pure noop
      VBruijn _      → pure noop
      Spec _         → pure noop -- inlineSpecMaybe?
      Var (VQBind q) → inlineMaybe q cs sArgs -- partial inline if produces / consumes labels
      x → error (toS (prettyTermRaw x) <> "\n" <> (concatMap ((++ "\n") . toS . prettyTermRaw) sArgs))
--    Case caseID scrut → use cases ≫= \c → MV.read c caseID ≫= \(br , d) → fuseMatch _ (pure scrut) br d

-- case-label is ideal,  case-case almost as good. otherwise args are involved and will require spec
fuseMatch ∷ Type → Term → BSM.BitSetMap ABS → Maybe ABS → SimplifierEnv s Term
fuseMatch retT scrut branches d = let noop = App (Match retT branches d) [scrut] in case scrut of
  -- trivial case-of-label
  Label l params → foldAbs (fromJust $ (branches BSM.!? qName2Key l) <|> d) params

  -- case-of-case: push outer case into each branch, then the inner case fuses with outer case output labels
  App (Match ty2 innerBranches _innerDefault) [innerScrut] → let
    pushCase (Lam ars free ty , body) = do
      branch ← simpleApp (Match ty branches d) [body]
      pure (Lam ars free ty , branch)
    in do
    optBranches ← innerBranches `forM` pushCase
    optD ← maybe (pure Nothing) (fmap Just . pushCase) d
    simpleApp (Match ty2 optBranches optD) [innerScrut]

  Var (VQBind q) → forceInline q ≫= \case
    Nothing → pure noop
    Just scrutInline → fuseMatch retT scrutInline branches d

  Case caseId _scrut → error $ show caseId

  -- opaque scrut = App | Arg ; this failed to produce a direct fusable, have to wait until args given
  -- un-inline the case to isolate structure
  -- fn-args are involved ⇒ annotate their collapsible structure at fn definition
  _opaque → do
    caseID ← addCase (branches , d)
    structure %= (caseID :)
--  pure (Case caseID opaque)
    pure noop
