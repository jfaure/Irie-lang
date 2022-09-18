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
import Data.List (unzip3 , foldr1)
-- The only optimisation worth doing is fusing Match with Labels
-- Most of the complexity here addresses fusion accross fn (partial) applications

-- * mk standalone fn for case + case-splits
-- * record arg shapes
-- ? conditional destructuring

-- All cases "eventually" receive structure; we can fuse unless opaque scrut | recursive

-- save structure / constants folded into each specialisation
data ArgShape
 = ShapeNone
 | ShapeLabel ILabel [ArgShape]
 | ShapeQBind QName
 deriving (Ord , Eq)

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
 , _cases       ∷ MV.MVector s (BSM.BitSetMap Expr , Maybe Expr) -- BranchIDs
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

-- Replace all label | const args with new deBruijn argNames (either bind to specialise or spec to respecialise)
mkSpec ∷ Either QName IName → Term → [Term] → SimplifierEnv s Term
mkSpec q body args = let
  (ret , bruijnN) = traverse solveArg args `runState` 0
  (  unstructuredArgs -- subExpressions of Labels , now deBruijn args
   , repackedArgs     -- original args with label subExprs replaced with deBruijn args
   , argShapes)
   = unzip3 ret
  solveArg ∷ Term → State Int ([Term] , [Term] , ArgShape)
  solveArg = \case
    Label l ars → traverse solveArg ars
      <&> \(a : ars) → foldl (\(u,r,s) (u',r',s') → (u ++ u' , [Label l (r ++ r')] , ShapeLabel l [s' , s])) a ars
    rawArg      → gets identity ≫= \bruijn → modify (1+) $> ([rawArg] , [VBruijn bruijn] , ShapeNone)
  in do
  spec ← simpleTerm (App body (concat repackedArgs))
  addSpec (either modName identity q) argShapes bruijnN spec
  pure (App spec (concat unstructuredArgs))

simplifyBindings ∷ IName → Int → Int → MV.MVector s Bind → ST s (FEnv s)
simplifyBindings modIName nArgs nBinds bindsV = do
  argSubs ← MV.generate nArgs (Var . VArg)
  br      ← MV.new 32
  cs      ← MV.new 32
  sp      ← MV.new nBinds -- TODO add specs to BindOK
  sb      ← MV.new 32
  (simpleBind `mapM` [0 .. nBinds - 1]) `execStateT` FEnv
    { _thisMod     = modIName
    , _cBinds      = bindsV
    , _self        = -1
    , _structure   = []
    , _argTable    = argSubs
    , _useArgTable = False
    , _inlineStack = emptyBitSet

    , _specCache   = sp -- a Map of ArgShapes → Spec for each bind
    , _specBound   = sb -- raw binds table
    , _specsLen    = 0
    , _bruijnArgs  = mempty

    , _branches    = br
    , _cases       = cs
    , _caseLen     = 0
    , _branchLen   = 0
    }

simpleBind ∷ Int → SimplifierEnv s Bind
simpleBind bindN = use cBinds ≫= \cb → MV.read cb bindN ≫= \b → do
  mod ← use thisMod
  self .= bindN
  MV.write cb bindN (BindOpt (complement 0) emptyBitSet (Core (Var (VQBind (mkQName mod bindN))) tyBot)) -- used to generate VBind here

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

inlineStructure ∷ QName → _ → _ → SimplifierEnv s _
inlineStructure q cs args = use thisMod ≫= \mod → let
  unQ = unQName q
  noInline = (Var (VQBind q))
  in do
  this ← use self
  is ← inlineStack <<%= (`setBit` unQ)
  fn ← if mod /= modName q || (is `testBit` unQ)
    then pure noInline
    else simpleBind unQ <&> \case
      BindOK o l r (Core inlineF ty) | worthInline _ args cs
        -- If recursive, we must spawn a specialisation. (we may as well cache specialisations anyway)
        → inlineF
      _ → noInline
  App fn <$> sequence args

-- ? static arg transformation vs partial specialisation
-- ? spawn specialisations for recursion
-- * unwrap args at App and bypass some cases

-- Is this worth inlining
-- | Does fn Match any of its args
-- | Does fn produce any Labels
worthInline fnInfo args caseWraps = True
  -- unfused cases have a dependency tree: (ScrutApp | ScrutArg) ⇒ each case: [Args] required to reduce
  -- * inline only happens upto cases/branches

-- Note. Since this performs beta-reduction on all args in scope,
-- if we beta-reduce an arg with a fn of itself (while deriving specialisations)
-- do not β-reduce it again: ie. Excessive calls to simpleTerm are incorrect
-- para helps clarify the recursion
simpleTerm ∷ Term → SimplifierEnv s Term
simpleTerm = RS.para $ \case
  VarF v → case v of
    VArg i   → use argTable ≫= \at → MV.read at i
    VQBind i → pure (Var (VQBind i))
  AppF f args → case fst f of
    -- paramorphism catches Abs so we can setup β-reduction env before recursing
    Abs argDefs free body ty → foldAbs argDefs free body ty (snd <$> args)
    _     → simpleApp (snd f) (snd <$> args)
  RecAppF f args → case fst f of
    -- paramorphism catches Abs so we can setup β-reduction env before recursing
    Abs argDefs free body ty → foldAbs argDefs free body ty (snd <$> args)
    _     → simpleApp (snd f) (snd <$> args)
  t → embed <$> sequence (fmap snd t)

-- one-step fusion
simpleApp ∷ SimplifierEnv s Term → [SimplifierEnv s Term] → SimplifierEnv s Term
simpleApp f args = let sArgs = sequence args in f ≫= \case
  App f2 args2             → simpleApp (pure f2) (args ++ (pure <$> args2)) -- can try again

  -- abs unnoticed by para (was inlined) ⇒ need to resimplify body, which is why case&branch extraction is important
  Abs argDefs free body ty → foldAbs argDefs free body ty args

  Instr i                  → simpleInstr i <$> sArgs
--Lens
  Case caseId scrut → error $ show caseId
  Match retT branches d | [scrut] ← args → fuseMatch retT scrut branches d
  opaqueFn → use structure ≫= \case
    [] → App opaqueFn <$> sArgs
    -- If we're building a scrutinee, partial inline upto the fusable structure
    cs → case opaqueFn of
      Var (VArg _)   → App opaqueFn <$> sArgs -- the arg is out of our scope atm
      Var (VQBind q) → inlineStructure q cs args -- partial inline if that simplifies anything
--    Case caseID scrut → use cases ≫= \c → MV.read c caseID ≫= \(br , d) → fuseMatch _ (pure scrut) br d

-- Perform β-reduction on an Abs. Have to simplify the body (again)
-- Note. if some arg is substituted with a fn of itself (while deriving specialisations),
-- do not β-reduce it there: Excessive calls to simpleTerm are incorrect
foldAbs ∷ [(Int , Type)] → BitSet → Term → Type → [SimplifierEnv s Term] → SimplifierEnv s Term
foldAbs argDefs _free body _ty args = use argTable ≫= \aT → do
  args' ← sequence args -- ? is it worth delaying this
  let (resArgDefs , trailingArgs , betaReducable) = partitionThese (align argDefs args')
  svUseAt ← useArgTable <<.= True
  sv ← betaReducable `forM` \((i,_ty) , arg) → ((i,) <$> MV.read aT i) <* MV.write aT i arg
  bodyOpt ← simpleTerm body -- re-simplify with args in scope
  useArgTable .= svUseAt
  sv `forM_` \(i , arg) → MV.write aT i arg

  when (not (null resArgDefs)) (traceM $ "resArgDefs! " <> show resArgDefs)
  pure $ case trailingArgs of
    []  → bodyOpt
    ars → App bodyOpt ars

-- case-label is ideal,  case-case almost as good. otherwise args are involved and will require spec
fuseMatch ∷ Type → SimplifierEnv s Term → BSM.BitSetMap Expr → Maybe Expr → SimplifierEnv s Term
fuseMatch retT scrut branches d = scrut ≫= \case
  -- Ideal case-of-label
  Label l params → let getTerm (Just (Core t _ty)) = t
    in simpleApp (pure $ getTerm ((branches BSM.!? qName2Key l) <|> d)) (pure <$> params)

  -- Also good: case-of-case: push outer case into each branch of the inner Case
  -- then the inner case can fuse with the outer cases output labels
  App (Match ty2 innerBranches _innerDefault) [innerScrut] → let
    pushCase (Core (Abs ars free body ty) _ty) = do
      branch ← simpleApp (pure $ Match ty branches d) [pure body]
      let newTy = case branch of { Abs _ _ _ t → t ; _ → tyBot } -- lost the Ty
      pure (Core (Abs ars free branch newTy) newTy)
    in do
    optBranches ← innerBranches `forM` pushCase
    optD ← maybe (pure Nothing) (fmap Just . pushCase) d
    pure (App (Match ty2 optBranches optD) [innerScrut])

  Case caseId scrut → error $ show caseId

  -- not fusable; scrut = App | Arg (this already failed to produce a direct fusable)
  -- un-inline the case to isolate structure
  -- fn-args are involved ⇒ annotate their collapsible structure at fn definition
  opaque → do
    caseID ← addCase (branches , d)
    structure %= (caseID :)
--  pure (Case caseID opaque)
    pure $ App (Match retT branches d) [opaque]
