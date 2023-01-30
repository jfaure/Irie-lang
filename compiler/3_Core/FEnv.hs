{-# Language TemplateHaskell #-}
module FEnv where -- (simplifyModule) where
import CoreSyn
import SimplifyInstr
import Prim
import PrettyCore
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.Map as M
import BitSetMap as BSM
import Data.Functor.Foldable as RS
import Control.Lens hiding ((:<))
import Data.List (unzip3)
import Control.Comonad
import Control.Comonad.Cofree

debug_fuse = True
normalise  = True
-- Inline everything and constant-fold

-- TODO identify ReCons => rewrite to Lens operations
-- make Dup nodes

-- Recursion-schemes histo based on distHisto fails to share all subcomputations
histo' :: forall t a. Recursive t => (Base t (Cofree (Base t) a) -> a) -> t -> a
histo' f = extract . h where
  h :: t -> Cofree (Base t) a
  h = (\bc -> f bc :< bc) . fmap h . project

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

-- ↓ fusion => β-env setup @ App (Lam) _ars
-- ↑ fusion; β-reduction & inlining ; λ lifting

-- specialisations are keyed on arg structure (labels | constants)
data FEnv s = FEnv
 { _structure  :: [CaseID] -- passed down to indicate we're building a fusable

 , _bruijnArgs :: V.Vector Term -- fresh argNames for specialisations
 , _fullNormalise :: Bool -- simplifying a 0 arity bind
   -- If bind has arity, it contains VBruijns thus recursively inlining won't terminate

 , _letBinds   :: MV.MVector s (MV.MVector s Bind)
 , _letNest    :: Int
 , _interpret  :: Bool -- inline, β-reduce and constant-fold everything
 }; makeLenses ''FEnv
type SimplifierEnv s = StateT (FEnv s) (ST s)

termSize :: Term -> Int -- TODO perhaps still avoid inlining large records / tycons
termSize term = cata go term `evalState` 0 where
  go = \case
    AppF f ars -> get >>= \n -> if n > 2 then pure n else modify (1+) *> ((\f ars -> f + sum ars) <$> f <*> sequence ars)
    _ -> pure 0

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
  -- Need to reverse unstructuredArgs since our deBruijns are assigned in reverse order

t1 = destructureArgs [VBruijn 0 , VBruijn 1]
t2 = destructureArgs [Label (QName 0) [VBruijn 0] , Label (QName 1) [VBruijn 1]]
t3 = destructureArgs [VBruijn 0 , VBruijn 1 , Var (VLetBind (QName 1)) , Label (QName 1) []]
t4 = destructureArgs [VBruijn 0 , VBruijn 1 , Var (VLetBind (QName 1)) , Label (QName 1) [Lit (Int 3)]]

-- TODO HACK letbinds may escape their scope !!
getLetSpec q argShapes = d_ ("warning: not robust if the let-bound escapes its scope") $ 
  use letBinds >>= \lb -> (lb `MV.read` modName q) >>= \bindVec -> MV.read bindVec (unQName q) <&> \case
    BindOK o (Core _inlineF _ty) -> fromMaybe (error "no bind-spec !") (bindSpecs o M.!? argShapes)
    x -> error $ show x

-- Inline partially an App or its specialisation if expect something to fuse
-- fully inline unconditionally if interpreting
-- True = letbind ; false = VQBind
-- TODO this checks argShapes at every QName application ..
specApp :: Bool -> QName -> wrapCases -> [Term] -> SimplifierEnv s Term
specApp isLetBind q _cs args = case isLetBind of
  True  -> let
    nest = modName q ; bindNm  = unQName q
    noInline = App (Var (VLetBind q)) args
    (bruijnN , unstructuredArgs , repackedArgs , argShapes) = destructureArgs args
    in -- d_ args $ d_ argShapes $ d_ repackedArgs $ d_ unstructuredArgs $ d_ "" $
    use letBinds >>= \lb -> (lb `MV.read` nest) >>= \bindVec -> MV.read bindVec bindNm >>= \case
    BindOK o expr@(Core inlineF _ty) | any (/= ShapeNone) argShapes ->
      case {-d_ (q , argShapes) $-} bindSpecs o M.!? argShapes of
      Just cachedSpec -> simpleApp cachedSpec unstructuredArgs
      Nothing -> if all (\case { ShapeNone -> True ; _ -> False }) argShapes then pure noInline else do
        let recGuard = LetSpec q argShapes
        MV.modify bindVec (\(BindOK (OptBind oLvl oSpecs) _t)
          -> BindOK (OptBind oLvl (M.insert argShapes recGuard oSpecs)) expr) bindNm

        -- fully simplify the specialised partial application (if it recurses then the spec is extremely valuable)
        let raw = App inlineF repackedArgs
            rawAbs = if bruijnN == 0 then raw else BruijnAbs bruijnN emptyBitSet raw -- TODO get the types also !

        -- ! the repacked args may contain VBruijns; free variables in the context the spec is being built
        specFn <- reSimpleTerm rawAbs

        when debug_fuse $ do
--        traceM $ show args <> "\n" <> show repackedArgs <> "\n" <> show unstructuredArgs
          traceM $ "raw spec " <> show bindNm <> " " <> show argShapes <> "\n => " <> prettyTermRaw rawAbs <> "\n"
          traceM $ "simple spec " <> prettyTermRaw specFn <> "\n"

        MV.modify bindVec (\(BindOK (OptBind oLvl oSpecs) _t)
          -> BindOK (OptBind oLvl (M.insert argShapes specFn oSpecs)) expr) bindNm

        -- TODO inline spec iff under some cases || fully β-reducing || small
--      if null unstructuredArgs then pure specFn else pure $ App specFn unstructuredArgs
        if null unstructuredArgs then pure recGuard else pure $ App recGuard unstructuredArgs
    _ -> pure noInline

  -- Don't specialise imported binds
  False -> let noInline = App (Var (VQBind q)) args in pure noInline

-- terms may contain VBruijns; free variables in the context this is being built
-- Setup identity substitution for free vars
-- TODO would be slightly more efficient to directly β-env since they will have to be incremented by bruijnN
reSimpleTerm raw = do
  prev <- bruijnArgs <<%= \v -> V.generate (V.length v) VBruijn
  simpleTerm raw <* (bruijnArgs .= prev)

--forceInline :: QName -> SimplifierEnv s (Maybe Term)
--forceInline q = simpleLetName (unQName q) <&> \case -- make a specialisation
--  BindOK _o (Core inlineF _ty) -> Just inlineF
--  _ -> Nothing

forceInlineLetBind q = let letDepth = modName q ; bindNm = unQName q
  in use letBinds >>= \lb -> (lb `MV.read` letDepth) >>= \b -> MV.read b bindNm <&> \case
    BindOK _o (Core inlineF _ty) -> Just inlineF
    _ -> Nothing

--simplifyBindings :: IName -> MV.MVector s Bind -> ST s (Maybe Specialisations)
simplifyModule :: Expr -> ST s Expr
simplifyModule mod = do
  letBinds' <- MV.new 16
  simpleExpr mod `evalStateT` FEnv
    { _structure   = []

    , _bruijnArgs  = mempty
    , _fullNormalise = False

    , _interpret   = False
    , _letBinds    = letBinds'
    , _letNest     = 0
    }

sT t = (bruijnArgs <<.= mempty) >>= \sv -> simpleTerm t <* (bruijnArgs .= sv)
simpleBind :: Bind -> SimplifierEnv s Bind
simpleBind b = case b of
  BindOK (OptBind optlvl specs) (Core t ty) -> if optlvl /= 0 then pure b
    else do
      svArity <- fullNormalise <<.= case t of { BruijnAbs{} -> False ; BruijnAbsTyped{} -> False ; _ -> True }
      r <- reSimpleTerm t <&> \case newT -> BindOK (OptBind (optlvl + 1) specs) $ Core newT ty
      r <$ (fullNormalise .= svArity)
  _x -> pure {-$ trace ("not bindok: " <> show bindN <> " " <> show x :: Text)-} WIP

simpleExpr :: Expr -> SimplifierEnv s Expr
simpleExpr (Core t ty) = reSimpleTerm t <&> \t' -> Core t' ty -- ?! how tf did this work when t was typoed instead of t'
simpleExpr PoisonExpr = pure PoisonExpr
simpleExpr x = pure $ d_ x PoisonExpr

-- one-step fusion on images of recursion (post β-reduction)
simpleApp :: Term -> [Term] -> SimplifierEnv s Term
simpleApp f sArgs = let noop = App f sArgs in case f of
  Instr i        -> pure $ if normalise then simpleInstr i sArgs else App (Instr i) sArgs
  Label l params -> pure (Label l (params ++ sArgs))
  App f1 args1   -> simpleApp f1 (args1 ++ sArgs) -- merge Args and retry
  BruijnAbsTyped n f (BruijnAbsTyped n2 f2 t aT2 rT2) aT _rT -> -- merge Abs and retry
    simpleApp (BruijnAbsTyped (n + n2) (f .|. f2) t (aT2 <> aT) rT2) sArgs
--Lens
--Case caseId scrut   -> error $ show caseId
  opaqueFn -> use structure >>= \case
--  [] -> pure noop
    cs -> case opaqueFn of -- If building a scrut, partial inline upto the fusable structure
      VBruijn _        -> pure noop
      Var (VQBind q)   -> specApp False q cs sArgs -- partial inline if produces / consumes labels
      Var (VLetBind q) -> specApp True  q cs sArgs -- partial inline if produces / consumes labels
      LetSpec q shp    -> getLetSpec q shp >>= \f -> pure $ App f sArgs -- TODO respecialise perhaps
      BruijnAbsTyped{} -> reSimpleTerm (App f sArgs) -- need to re-enter a β-env
      BruijnAbs     {} -> reSimpleTerm (App f sArgs) -- need to re-enter a β-env
      x -> error ("bad Fn: " <> toS (prettyTermRaw x) <> "\n" <> (concatMap ((++ "\n") . toS . prettyTermRaw) sArgs))

-------------------
-- Bruijn β-envs --
-------------------
readVBruijn v = use bruijnArgs <&> \vec -> if v < V.length vec then vec V.! v
  else VBruijn v -- error $ (show v <> " >= " <> show (V.length vec))

-- \a b => ((\x => a + b) _)
-- free variables must be decremented on binder removal !
-- isApp indicates substituting args, else an identity traversal needs to increment prev args
bruijnEnv :: Int -> Bool -> SimplifierEnv s Term -> [Term] -> SimplifierEnv s Term
bruijnEnv _n isApp f args = do
  let new = V.reverse (V.fromList args)
      l = V.length new
--when (n /= l) (error "")
  prev  <- use bruijnArgs
  -- need to increment any debruijn free variables in the prev arguments
  -- (ie. when simplifying functions / making specialisations we're working under some debruijn abstractions)
  prev' <- (bruijnArgs .= V.generate (V.length prev) (\i -> VBruijn (if isApp then i else i + l))) *> mapM simpleTerm prev
  bruijnArgs .= new <> prev'
  f <* (bruijnArgs .= prev)

-- Note. if we β-reduce an arg with some fn of itself (while deriving specialisations)
-- must not β-reduce it again: ie. Excessive calls to simpleTerm are incorrect. histo guarantees a single pass
simpleTerm :: Term -> SimplifierEnv s Term
simpleTerm = histo' betaTermF

-- When fully normalising, need to inline functions, iff args contain no VBruijns
betaTermF :: TermF (Cofree TermF (SimplifierEnv s Term)) -> SimplifierEnv s Term
betaTermF tt = let
  inferBlock lets go = do
    traceM "incBlock"
    nest <- letNest <<%= (1+)
    use letBinds >>= \lvl -> V.thaw (snd <$> lets) >>= MV.write lvl nest
    go <* (letNest %= \x -> x - 1) <* traceM "decBlock" 
  in case tt of -- d_ (embed $ Question <$ tt) tt of
  VarF (VLetBind q) | normalise -> forceInlineLetBind q <&> fromMaybe (error "failed to inline") <&> \case
    BruijnAbsTyped{} -> Var (VLetBind q)
    BruijnAbs{} -> Var (VLetBind q)
    x -> x
  VBruijnF v -> readVBruijn v
  -- unapped abstractions => make an identity app
  BruijnAbsF n free body -> BruijnAbs n free <$> bruijnEnv n False (extract body) [VBruijn i | i <- [n-1,n-2 .. 0]]
  BruijnAbsTypedF n free body aT rT -> (\b -> BruijnAbsTyped n free b aT rT) <$>
    bruijnEnv n False (extract body) [VBruijn i | i <- [n-1,n-2 .. 0]]
  AppF f args
    | BruijnAbsF n free body <- unwrap f -> let l = length args in
      traverse extract args >>= \ars -> bruijnEnv n True (extract body) ars <&> \r ->
        -- TODO Abs before simplification
        if l < n then _BruijnAbs (n - l) free r else r
    | BruijnAbsTypedF n free body argsT retT <- unwrap f -> let l = length args in
      traverse extract args >>= \ars -> bruijnEnv n True (extract body) ars <&> \r ->
        if l < n then _BruijnAbsTyped (n - l) free r (drop l argsT) retT else r
--  | normalise , VarF (VQBind q)   <- unwrap f -> forceInline q <&> fromMaybe (error "failed to inline")
--    >>= \f -> traverse extract args >>= \ars -> reSimpleTerm $ App f ars
    | normalise , VarF (VLetBind q) <- unwrap f -> do
      f <- forceInlineLetBind q <&> fromMaybe (error "failed to inline")
      -- TODO not V.null but iff args contain no Bruijns that may stall fuseMatch, simplify branches and loop on rec
      ars <- traverse extract args
      bArgs <- use bruijnArgs
      noTopArity <- use fullNormalise
      if V.null bArgs || noTopArity then reSimpleTerm (App f ars) else pure $ App (Var (VLetBind q)) ars
    | otherwise -> (embed <$> traverse extract tt) >>= \(App f args) -> simpleApp f args
--  opaque -> App opaque <$> args
  LetBlockF lets -> inferBlock lets $ LetBlock <$> lets `forM` \(lm , bind) -> (lm ,) <$> simpleBind bind
  LetBindsF lets inE -> inferBlock lets $ do
    newLets <- lets `forM` \(lm , bind) -> (lm ,) <$> simpleBind bind
    newInE  <- {-simpleTerm-} (extract inE)
    pure (LetBinds newLets newInE)
  CaseBF s r b d -> if normalise
    then extract s >>= \scrut -> postFuse scrut r (extract <$> b) (extract <$> d)
    else (fuseMatch tt & extract) >>= \result -> case result of
      -- if no pre fusion can retry after simplifying the scrut;
      -- TODO should do this pre- simplifying branches
      CaseB scrut retT branches d -> postFuse scrut retT (pure <$> branches) (pure <$> d)
      x -> pure x
  MatchBF{} -> error ""
  t -> embed <$> traverse extract t

-- Simple β-reduction of case. As usual excessive simplification is incorrect,
-- eg. if fully normalising we would loop by inlining recursive calls even if non-recursive branch is taken
postFuse :: Term -> Type -> BSM.BitSetMap (SimplifierEnv s Term) -> Maybe (SimplifierEnv s Term) -> SimplifierEnv s Term
postFuse scrut ret branches d' = case scrut of
  Label l params -> case (branches BSM.!? qName2Key l) <|> d' of
    Just body | null params -> body
    Just body -> (\b -> App b params) <$> body
    Nothing -> error $ "panic: label not found: " <> show l <> " : " <> show params <> "\n; " <> show (BSM.keys branches)
  _ -> CaseB scrut ret <$> sequence branches <*> sequence d'

-- attempt Fusion before β-reducing anything
-- Also attempt fusion after β-reducing the scrut
-- We must limit ourselves to setting up histories and delegate everything to betaTermF
-- We Cannot rewrite history that depends on result of scrut
-- ! Any duplicate traversal in a β-env may overwrite debruijn subs so is incorrect
fuseMatch :: TermF (Cofree TermF (SimplifierEnv s Term)) -> Cofree TermF (SimplifierEnv s Term)
--fuseMatch :: Type -> CTS s -> BitSetMap (LamBEnv , CTS s) -> Maybe (LamBEnv , CTS s) -> CTS s
fuseMatch hist@(CaseBF scrut retT branches d) = case unwrap scrut of
  -- trivial case-of-label Delay simplifying case-alts until we setup β-env:
  LabelF l params -> case (branches BSM.!? qName2Key l) <|> d of
    Just body | null params -> extract body :< CastF BiEQ body
    Just body -> betaTermF (AppF body params) :< AppF body params -- Can avoid traversing the other branches this way
    Nothing -> error $ "panic: label not found: " <> show l -- <> " : " <> show params <> "\n; " <> show (BSM.keys branches)
--  -- case-of-case: push outer case into each branch,
--  -- then the inner case fuses with outer case output labels
  CaseBF innerScrut ty2 innerBranches innerDefault -> let
    pushCase innerBody = fuseMatch (CaseBF innerBody retT branches d) -- TODO need inner retT ?
    optBranches = pushCase <$> innerBranches
    optD        = pushCase <$> innerDefault
    in fuseMatch (CaseBF innerScrut ty2 optBranches optD)

-- Force sub-expression upto structure if possible
-- Theres no useful history post-inline, so QuestionF is a good candidate to erase it
  VarF (VLetBind q) -> let inlined = forceInlineLetBind q <&> fromMaybe (error "failed to inline")
    in fuseMatch (CaseBF (inlined :< QuestionF) retT branches d)
--VBruijnF{} -> fuseMatch (CaseBF (extract scrut :< scrut) retT branches d)
--AppF{}     -> fuseMatch (CaseBF (extract scrut :< scrut) retT branches d)
-- LetSpec q sh -> error $ show q --Spec q -> inlineSpec q >>= \s -> fuseMatch retT s branches d

  _noop -> (embed <$> traverse extract hist) :< hist
