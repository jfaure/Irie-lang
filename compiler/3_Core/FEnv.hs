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
-- The only optimisation worth doing is fusing Match with Labels
-- Most of the complexity here addresses fusion accross fn (partial) applications

-- * mk standalone fn for case + case-splits
-- * record arg shapes
-- ? conditional destructuring

-- ? static arg transformation vs partial specialisation
-- ? spawn specialisations for recursion
-- * unwrap args at App and bypass some cases

-- All cases "eventually" receive structure; we can fuse unless opaque scrut | recursive

-- save structure / constants folded into each specialisation
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
 , _inlineStack ∷ BitSet

 , _specCache   ∷ MV.MVector s (M.Map [ArgShape] IName) -- Bind → Spec cache
 , _specBound   ∷ MV.MVector s (Int , Term) -- INamed fresh specialisations: (bruijnN , body)
 , _specsLen    ∷ Int
 , _bruijnArgs  ∷ V.Vector Term -- fresh argNames for specialisations

-- name and extract all cases and branches (since frequently duplicated and fused)
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
  s  ← (branches <.=) =≪ (if MV.length br <= n then MV.grow br 32 else pure br)
  n <$ MV.write s n newBranch

addSpec ∷ IName → [ArgShape] → Int → Term → SimplifierEnv s QName
addSpec bindINm argShapes bruijnN spec = do
  s  ← specsLen <<%= (1+)
  use specCache ≫= \sc → MV.modify sc (M.insert argShapes s) bindINm
  sb ← use specBound
  specs  ← (specBound <.=) =≪ (if MV.length sb <= s then MV.grow sb 32 else pure sb)
  mkQName bindINm s <$ MV.write specs s (bruijnN , spec)

-- Replace all label | const args with new deBruijn argNames
-- q is (either spec to respecialise or bind to specialise)
mkSpec ∷ Either QName IName → Term → [Term] → SimplifierEnv s Term
mkSpec q body args = let
  (ret , bruijnN) = traverse solveArg args `runState` 0
  (  unstructuredArgs -- subExpressions of Labels , now deBruijn args
   , repackedArgs     -- original args with label subExprs replaced with deBruijn args
   , argShapes)
   = unzip3 ret
  solveArg ∷ Term → State Int ([Term] , [Term] , ArgShape)
  solveArg arg = case arg of
    Var (VQBind q) → pure ([] , [arg] , ShapeQBind q)
    Label l ars → traverse solveArg ars <&> \case
      [] → ([] , [arg] , ShapeLabel l []) -- lone label is like a constant VQBind
      (a : ars) → let
        go (u,r,s) (u',r',s') = (u ++ u' , [Label l (r ++ r')] , ShapeLabel l [s' , s])
        in foldl go a ars
    rawArg         → gets identity ≫= \bruijn → modify (1+) $> ([rawArg] , [VBruijn bruijn] , ShapeNone)
  in do
  let rawSpec = App body (concat repackedArgs)
  traceM "raw spec"
  traceM (prettyTermRaw rawSpec)
  spec ← simpleTerm rawSpec
  traceM "simple spec"
  traceM (prettyTermRaw spec)
  traceM ""

  s ← addSpec (either modName identity q) argShapes bruijnN spec
  -- TODO inline the spec again if we're wrapping more structure!
  case unQName s of
    0 → inlineSpec s <&> \f → App f (concat unstructuredArgs)
    _ → pure (App (Spec s) (concat unstructuredArgs))

inlineStructure ∷ QName → wrapCases → [Term] → SimplifierEnv s Term
inlineStructure q cs args = use thisMod ≫= \mod → let
  unQ = unQName q
  noInline = App (Var (VQBind q)) args
  in do
  is ← inlineStack <<%= (`setBit` unQ)
  if mod /= modName q || (is `testBit` unQ)
    then pure noInline
    else simpleBind unQ ≫= \case
      BindOK _o _l _r (Core inlineF _ty) | worthInline _ args cs
        -- If recursive, we must spawn a specialisation. (we may as well cache them anyway)
        → mkSpec (Right (unQName q)) inlineF args
      _ → pure (App noInline args)

-- Is this worth inlining
-- | Does fn Match any of its args
-- | Does fn produce any Labels
worthInline fnInfo args caseWraps = True
  -- unfused cases have a dependency tree: (ScrutApp | ScrutArg) ⇒ each case: [Args] required to reduce
  -- * inline only happens upto cases/branches

simplifyBindings ∷ IName → Int → Int → MV.MVector s Bind → ST s (FEnv s)
simplifyBindings modIName nArgs nBinds bindsV = do
  argSubs ← MV.generate nArgs (Var . VArg)
  br      ← MV.new 32
  cs      ← MV.new 32
  sc      ← MV.generate nBinds mempty -- TODO add specs to BindOK
  sb      ← MV.new 32
  ((simpleBind `mapM` [0 .. nBinds - 1]) *> traceSpecs nBinds) `execStateT` FEnv
    { _thisMod     = modIName
    , _cBinds      = bindsV
    , _self        = -1
    , _structure   = []
    , _argTable    = argSubs
    , _useArgTable = False
    , _inlineStack = emptyBitSet

    , _specCache   = sc -- a Map of ArgShapes → Spec for each bind
    , _specBound   = sb -- raw binds table
    , _specsLen    = 0
    , _bruijnArgs  = mempty

    , _branches    = br
    , _cases       = cs
    , _caseLen     = 0
    , _branchLen   = 0
    }

-- always inline?
inlineSpec q = use specBound ≫= \sb → snd <$> MV.read sb (unQName q)

traceSpecs ∷ Int → SimplifierEnv s ()
traceSpecs nBinds = do
  sb ← use specBound
  sl ← use specsLen
  traceM "-- Specs --"
  [0..sl-1] `forM_` \i → MV.read sb i ≫= \(b , t) → traceM ("spec " <> show i <> " = Bruijn(" <> show b <> "). " <> prettyTermRaw t)
  sc ← use specCache
  [0..nBinds-1] `forM_` \i → MV.read sc i ≫= \m → if M.null m then pure () else traceM $ "π" <> show i <> " specs " <> show m

simpleBind ∷ Int → SimplifierEnv s Bind
simpleBind bindN = use cBinds ≫= \cb → MV.read cb bindN ≫= \b → do
  mod ← use thisMod
  self .= bindN
  MV.write cb bindN (BindOpt (complement 0) emptyBitSet (Core (Var (VQBind (mkQName mod bindN))) tyBot))

  (new , isRec , l) ← case b of
    BindOK n l isRec body@(Core t ty) → if n /= 0 then pure (body , isRec , l)
      else fmap (,isRec,l) $ simpleTerm t <&> \case
      -- catch top level partial application (ie. extra implicit args)
      App (Instr (MkPAp _n)) (f2 : args2) → let
        (arTs , retT) = getArrowArgs ty
        in Core (PartialApp arTs f2 args2) retT
      newT → Core newT ty
    x → pure $ traceShow x (PoisonExpr , False , False)

  let newB = BindOK 1 l isRec new
  newB <$ MV.write cb bindN newB

-- Note. Since this performs beta-reduction on all args in scope,
-- if we beta-reduce an arg with a fn of itself (while deriving specialisations)
-- do not β-reduce it again: ie. Excessive calls to simpleTerm are incorrect
-- para helps clarify the recursion, each step gives (pre-image , image) of the recursion
simpleTerm ∷ Term → SimplifierEnv s Term
simpleTerm = RS.para $ \case
  VarF v → case v of
    VArg i   → use argTable ≫= \at → MV.read at i -- ≫= \a → a <$ traceM (show i <> " β " <>  prettyTermRaw a) 
    VQBind i → pure (Var (VQBind i))
    v        → pure (Var v) -- ext | foreign
  SpecF q     → inlineSpec q
  AppF f args → case fst f of
    -- paramorphism catches Abs so we can setup β-reduction env before running f
    -- ! This assumes simpleTerm never changes argDefs
    Abs ((Lam argDefs free _ty , _body)) → traverse snd args ≫= \ars → inBetaEnv argDefs free ars (snd f) <&> \(_,_,r) → r
    _     → snd f ≫= \rawF → traverse snd args ≫= simpleApp rawF
  RecAppF f args → case fst f of
    Abs ((Lam argDefs free _ty , _body)) → traverse snd args ≫= \ars → inBetaEnv argDefs free ars (snd f) <&> \(_,_,r) → r
    _     → snd f ≫= \rawF → traverse snd args ≫= simpleApp rawF
  t → embed <$> sequence (fmap snd t)

inBetaEnv ∷ [(Int , Type)] → BitSet → [Term] → SimplifierEnv s a → SimplifierEnv s ([(Int , Type)] , [Term] , a)
inBetaEnv argDefs _free args go = let
  (resArgDefs , trailingArgs , betaReducable) = partitionThese (align argDefs args)
  in do
  svUseAt ← useArgTable <<.= True
  aT ← use argTable
  sv ← betaReducable `forM` \((i,_ty) , arg) → ((i,) <$> MV.read aT i) <* MV.write aT i arg
  r ← go
  useArgTable .= svUseAt
  sv `forM_` \(i , arg) → MV.write aT i arg
  pure (resArgDefs , trailingArgs , r)

-- Perform β-reduction on an Abs. Have to simplify the body (again)
-- Note. if some arg is substituted with a fn of itself (while deriving specialisations),
-- do not β-reduce it there: Excessive calls to simpleTerm are incorrect
foldAbs ∷ ABS → [Term] → SimplifierEnv s Term
foldAbs (Lam argDefs free _ty , body) args = do
  (resArgDefs , trailingArgs , bodyOpt) ← inBetaEnv argDefs free args (simpleTerm body)
  when (not (null resArgDefs)) (traceM $ "resArgDefs! " <> show resArgDefs)
  pure $ case trailingArgs of
    []  → bodyOpt
    ars → App bodyOpt ars

-- one-step fusion
simpleApp ∷ Term → [Term] → SimplifierEnv s Term
simpleApp f sArgs = case f of
  Instr i      → pure (simpleInstr i sArgs)
  App f2 args2 → simpleApp f2 (sArgs ++ args2) -- can try again

  -- app-abs uncaught by para (was inlined) ⇒ need to resimplify body, which is why case&branch extraction is important
--Abs (Lam argDefs free ty , body) → foldAbs argDefs free body ty sArgs
  Abs _ → error "" -- foldAbs argDefs free body ty sArgs

--Lens
--Case caseId scrut → error $ show caseId
  Match retT branches d | [scrut] ← sArgs → do
    -- regrettably the base functor doesn't realise Expr also contains Terms
    br ← branches `forM` \((Lam ars free ty , body)) → simpleTerm body <&> \body' → (Lam ars free ty , body')
    fuseMatch retT scrut br d
  opaqueFn → let noop = App opaqueFn sArgs in use structure ≫= \case
    [] → pure noop
    -- If we're building a scrutinee, partial inline upto the fusable structure
    cs → case opaqueFn of
      Var (VArg _)   → pure noop
      VBruijn _      → pure noop
      Var (VQBind q) → inlineStructure q cs sArgs -- partial inline if that simplifies anything
      x → error (show x)
--    Case caseID scrut → use cases ≫= \c → MV.read c caseID ≫= \(br , d) → fuseMatch _ (pure scrut) br d

-- case-label is ideal,  case-case almost as good. otherwise args are involved and will require spec
fuseMatch ∷ Type → Term → BSM.BitSetMap ABS → Maybe ABS → SimplifierEnv s Term
fuseMatch retT scrut branches d = case scrut of
  -- Ideal case-of-label
  Label l params → foldAbs (fromJust $ (branches BSM.!? qName2Key l) <|> d) params

  -- Also good: case-of-case: push outer case into each branch of the inner Case
  -- then the inner case can fuse with the outer cases output labels
  App (Match ty2 innerBranches _innerDefault) [innerScrut] → let
    pushCase (Lam ars free ty , body) = do
      branch ← simpleApp (Match ty branches d) [body]
      pure (Lam ars free ty , branch)
    in do
    optBranches ← innerBranches `forM` pushCase
    optD ← maybe (pure Nothing) (fmap Just . pushCase) d
    pure (App (Match ty2 optBranches optD) [innerScrut])

  Case caseId _scrut → error $ show caseId

  -- not fusable; scrut = App | Arg (this already failed to produce a direct fusable)
  -- un-inline the case to isolate structure
  -- fn-args are involved ⇒ annotate their collapsible structure at fn definition
  opaque → do
    caseID ← addCase (branches , d)
    structure %= (caseID :)
--  pure (Case caseID opaque)
    pure $ App (Match retT branches d) [opaque]
