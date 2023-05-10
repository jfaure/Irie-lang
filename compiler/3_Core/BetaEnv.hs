{-# Language TemplateHaskell #-}
module BetaEnv where
import CoreSyn
import Data.Functor.Foldable as RS
import PrettyCore
import BitSetMap as BSM
import SimplifyInstr
import MUnrolls
import Control.Lens
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.Map as M
import Data.List (unzip3)

-- another Abs inside a β-env smaller than total env requires "inserting" more args
-- this more or less forces us to copy the env, which ruins β-optimal sharing of subcomputations

debug_fuse = True

data FEnv s = FEnv
 { _letBinds :: MV.MVector s (MV.MVector s Bind)
 , _letNest  :: Int
 }; makeLenses ''FEnv
type SimplifierEnv s = StateT (FEnv s) (ST s)

getBruijnAbs = \case
  BruijnAbs n body -> Just (n , body)
  BruijnAbsTyped n body _ _ -> Just (n , body)
  _ -> Nothing

type Lvl = Int
data Sub = TSub (V.Vector Sub) Lvl Term deriving Show -- eLen lvl term
type Env = (V.Vector Sub , [Sub]) -- [(Int , Term)]) -- length of argEnv (needs to remain consistent across paps
isEnvEmpty (subs , _tArgs) = V.null subs
type Seed = (Lvl , Env , Term) -- expected eLen may be < envlen since tsubs eLen can increase

-- # abs
--   +lvl -> inc subbed in vbruijns later
-- # app abs -> setup β-env
-- # inline fn -> possibly re-app

-- !! VBruijn sub-chain
-- # sub-ABS
--   * body VBruijns must skip over already apped trailingArgs (ie. == eLen)
--   * stacked VBruijn subs may refer again to larger env
-- # subVBruijn (env contains unsubstituted vbruijns)
--   = keep subbing and use sub context info
--
-- ?? env = remArgs .. ars .. env (free-vars are valid at env, captured vars are valid at al + length remArgs)
-- ! if body β-reduces into an abs then that abs skips these claimed args
-- ! abs args are valid at eLen , but free-vars are valid at atLen
-- newArgs .. _atLen@freeVars (can't delete '..' because chainSubs may need the middle)
-- Can't trim the env since argSubs may refer to larger env

--  ! Can't instantly simplify args to an App in case f contains more bruijnAbs. Also VBruijns may need relevelling
--  TODO this may duplicate work if simplified twice at the same lvl; counting on dup nodes + β-optimality to fix this

mkBruijnArgSubs l n = let env = mempty -- doesn't matter since bruijnLevel terminates
  in V.generate n (\i -> TSub env l (VBruijnLevel (l - i - 1)))

-- fuse: β-reduce and eliminate as many case-labels as possible (case-case , pap-spec , inline)
-- ! seed term and trailingArgs may have different envs
-- ! inlining needs to watch free-vars and VBruijn level differences
fuse :: forall s. Seed -> SimplifierEnv s (TermF (Either Term Seed))
fuse (lvl , env@(argEnv , trailingArgs) , term) = let
  eLen = V.length argEnv
  unSub (TSub prevArgEnv prevLvl arg) | prevLvl == lvl = Right (lvl , (prevArgEnv , mempty) , arg)
 -- unSub (TSub prevArgEnv prevLvl arg) = traceShow (prevLvl , lvl) $ Right (lvl , (prevArgEnv , mempty) , arg)

  in case term of
  App f args -> fuse (lvl , (argEnv , (TSub argEnv lvl <$> args) <> trailingArgs) , f)
  abs | Just (n , body) <- getBruijnAbs abs -> if null trailingArgs
    then case getBruijnAbs body of -- not β-reducing => spawn bruijn arg subs
      Just (m , b2) -> fuse (lvl , env , BruijnAbs (m + n) b2)
      _ -> pure $ BruijnAbsF n (Right (lvl + n , (mkBruijnArgSubs (lvl + n) n <> argEnv , mempty) , body))
    else claimArgs n body trailingArgs where
      claimArgs :: Int -> Term -> [Sub] -> SimplifierEnv s (TermF (Either Term Seed))
      claimArgs n body trailingArgs = let
        (ourArgs , remArgs) = splitAt n trailingArgs
        l = length ourArgs
        in case compare l n of
          EQ -> let nextEnv = V.reverse (V.fromList ourArgs) -- <&> patchAbs l
            in fuse (lvl , (nextEnv <> argEnv , remArgs) , body)
          LT -> claimArgs l (BruijnAbs (n - l) body) trailingArgs
          GT -> error "impossible"

  VBruijnLevel l -> pure $ let v = lvl - l - 1
    in if null trailingArgs then VBruijnF v else AppF (Left (VBruijn v)) (unSub <$> trailingArgs)

  -- env contains raw args to simplify, at the new lvl for any bruijns subbed in
  -- This duplicates work if simplifying the same arg twice at the same lvl - need β-optimality
  VBruijn i -> if i >= eLen then error $ show (i , eLen , env) else
    argEnv V.! i & \(TSub prevEnv prevLvl argTerm) -> -- if lvl /= prevLvl then error $ show (lvl , prevLvl) else
      fuse (lvl , (prevEnv , trailingArgs) , argTerm)

  -- inlineLetBind: lvl == 0 means this fully reduces (won't produce a function)
  Var (VLetBind q) | lvl == 0 -> use letBinds >>= \lb -> (lb `MV.read` modName q)
    >>= \bindVec -> MV.read bindVec (unQName q) >>= simpleBind lvl (argEnv , []) >>= \b -> case b of
      BindOK _ (nL , letCapture) (Core inlineF _ty) -> let
        env' = (V.drop (V.length argEnv - nL) argEnv , trailingArgs)
        in MV.write bindVec (unQName q) b -- in case this is first time seeing the bind
          *> fuse (lvl , env' , inlineF)
      x -> error $ show x

  Var (VLetBind q) | not (null trailingArgs) -> specApp lvl (argEnv , []) q
    =<< (trailingArgs `forM` \(TSub e l t) -> simpleTerm' l (e , []) t)

  LetSpec q sh | lvl == 0 -> use letBinds >>= \lb -> (lb `MV.read` modName q)
    >>= \bindVec -> MV.read bindVec (unQName q) >>= simpleBind lvl (argEnv , []) >>= \b -> MV.write bindVec (unQName q) b *> case b of
      BindOK (OptBind _ shps) _ _ -> case shps M.!? sh of
        Nothing -> error $ show (modName q , unQName q) <> ": " <> show shps -- pure (LetSpecF q sh) -- ?! error
        Just t  -> fuse (lvl , env , t)

  Label l ars -> pure $ LabelF l
    $  (Right . (lvl , (argEnv , mempty) ,) <$> ars)
    <> (unSub <$> trailingArgs)

  -- ? where do params come from if no trailing args here
  -- TODO what if stacking case-cases
--CaseSeq n scrut retT branches d -> if not (null trailingArgs) then _ else
--  simpleTerm' lvl (argEnv , []) (BruijnAbs n scrut)
--  >>= fuseCase lvl argEnv trailingArgs retT branches d
  CaseSeq n scrut retT branches d -> if not (null trailingArgs) then _ else
    simpleTerm' lvl (argEnv , []) scrut
    >>= fuseCase lvl (V.drop n argEnv) trailingArgs retT branches d -- keep same lvl

  CaseB scrut retT branches d -> simpleTerm' lvl (argEnv , []) scrut --scrut has no trailingArgs
    >>= fuseCase lvl argEnv trailingArgs retT branches d

  -- Try before and after forcing the scrut
  -- TODO other lenses ; trailingArgs
  TTLens obj [f] LensGet -> case obj of
    l@Label{} -> error $ "Lensing on a label: " <> show (l , f)
    LetBlock l -> case V.find ((==f) . iName . fst) l of
      Just x -> pure $ Right . (lvl,env,) <$> (\(Core t _ty) -> project t) (naiveExpr (snd x))
    Tuple l -> pure $ Right . (lvl,env,) <$> project (l V.! unQName (QName f))
    scrut | null trailingArgs -> simpleTerm' lvl env scrut >>= \case
      Tuple l -> pure $ Left <$> project (l V.! unQName (QName f))
      LetBlock l -> case V.find ((==f) . iName . fst) l of
        Just x -> pure $ Left <$> (\(Core t _ty) -> project t) (naiveExpr (snd x))
      opaque -> pure $ TTLensF (Left opaque) [f] LensGet

  LetBlock lets | not (null trailingArgs) -> error $ show trailingArgs -- TODO Why
  LetBlock lets | null trailingArgs ->
    inferBlock lets (\_ -> LetBlockF <$> lets `forM` \(lm , bind) -> (lm ,)
      <$> simpleBind lvl (argEnv , mempty) bind)
  LetBinds lets inE -> inferBlock lets $ \_ -> do
    newLets <- lets `forM` \(lm , bind) -> (lm ,) <$> simpleBind lvl (argEnv , mempty) bind
    newInE  <- simpleTerm' lvl env inE -- incl trailingArgs
    pure $ if lvl == 0 then Left <$> project newInE else LetBindsF newLets (Left newInE)

  x -> pure $ if null trailingArgs
    then Right . (lvl , env ,) <$> project x
    else AppF (Right (lvl , (argEnv , mempty) , x)) (unSub <$> trailingArgs)

fuseCase lvl argEnv trailingArgs retT branches d tt = let
  idEnv = mkBruijnArgSubs lvl (V.length $ fst env)
  env = (argEnv , trailingArgs)
  in case tt of
    -- case-label: params are already β-d at this lvl, so idSubs (not ideal solution though)
    Label l params -> case branches BSM.!? qName2Key l <|> d of
      Just body -> fuse (lvl , (argEnv , (params <&> TSub idEnv lvl) <> trailingArgs) , body)
      Nothing -> error $ "panic: no label: " <> show l <> " : " <> show params <> "\n; " <> show (BSM.keys branches)
    -- case-case: push(copy) outer case to each branch, then the inner case output fuses with outer case labels
    CaseB innerScrut ty2 innerBranches innerDefault -> let
      pushCase = \case -- this will produce a case-label for each branch
        -- case (\p1..p2 -> scrut) of branches
        -- (\p1..p2 C -> ) (p1..p2 -> scrut) (\case branches) -- Thus branches aren't touched by params
        BruijnAbs n innerOutput -> BruijnAbs n (CaseSeq n innerOutput retT branches d)
     -- BruijnAbs n innerOutput -> CaseSeq n innerOutput retT branches d
        BruijnAbsTyped{} -> _
     -- c@CaseB{} -> error $ show c
        innerOutput             -> CaseB innerOutput retT branches d
      in fuseCase lvl argEnv trailingArgs ty2 (pushCase <$> innerBranches) (pushCase <$> innerDefault) innerScrut
    -- no-fusion
    CaseSeq n innerScrut ty2 innerBranches innerDefault -> _
    opaqueScrut -> pure $ CaseBF (Left opaqueScrut) retT (Right . (lvl,env,) <$> branches)
                                                         (Right . (lvl,env,) <$> d)

-- case-case notes:
-- case-case: push/copy outer case to each branch, then the inner case output fuses with outer case labels
-- Scrut is pre β-reduced , fuse then β-reduce branches and d (after fusion = a single one)
-- TODO (?) need to inc args within the pushed case (normally case-Abs are distinct, but now we're stacking them)

    -- case (\p1..p2 -> scrut) of branches
    -- => \p1..p2 -> case scrut of branches
    -- TODO this bruijnAbs applies to the scrut but NOT the branches/d !
    -- | make a new fn that separate scrut/branches (not possible with current syntax)
    -- | New syntax: case-branches to separate scrut from branches and allow \p1..pn S -> pass in branches
    -- | force increment all bruijns in branches (complicated when meeting more bruijnAbs)
    -- | Wrap (blocks pattern matching and too weird)
    -- | Rewrite case-case to resolve all without returning (inner case usually scruts an arg so irreducable)
    -- | Leave the fn in the scrut (Then need to partition trailingArgs to scrut and to branch output)
    -- | case-branches are let-binds (ie. have explicit captures)
 -- BruijnAbs n innerOutput -> BruijnAbs n (CaseB innerOutput retT branches d) -- A case-label
 -- BruijnAbsTyped{} -> _
 -- innerOutput -> CaseB innerOutput retT branches d -- error ""
--pushCase innerOutput = did_ $ CaseB innerOutput retT branches d -- A case-label

inferBlock lets go = do
  nest <- letNest <<%= (1+)
  v <- use letBinds >>= \lvl -> V.thaw (snd <$> lets) >>= \v -> MV.write lvl nest v $> v
  go v <* (letNest %= \x -> x - 1) -- <* traceM "decBlock" 

-- TODO how to avoid duplicate simplifications? ie. iff no VBruijns to solve: isEnvEmpty
simpleBind lvl env b = case b of
--BindOK _ _ PoisonExpr -> pure b
  BindOK (OptBind optLvl specs) free (Core t ty) -> if isEnvEmpty env && optLvl /= 0 then pure b else do
    newT <- simpleTerm' lvl env t
    pure (BindOK (OptBind ({-optLvl +-} 1) specs) free (Core newT ty))
  x -> error $ show x

simpleTerm' :: Int -> Env -> Term -> SimplifierEnv s Term
simpleTerm' lvl env t = hypoM constFoldF fuse (lvl , env , t)
simpleTerm t = do
  letBinds' <- MV.new 64 -- max let-depth
  simpleTerm' 0 (mempty , mempty) t `evalStateT` FEnv letBinds' 0

simpleExpr :: Expr -> ST s Expr
simpleExpr (Core t ty) = simpleTerm t <&> \t -> Core t ty
simpleExpr _ = pure PoisonExpr

constFoldF :: TermF Term -> Term
constFoldF = \case
  AppF (Instr i) args -> simpleInstr i args
  AppF (App g args) brgs -> constFoldF (AppF g (args <> brgs))
  x -> embed x

------------------
-- Specialisations
------------------
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

specApp :: forall s. Lvl -> Env -> QName -> [Term] -> SimplifierEnv s (TermF (Either Term Seed))
specApp lvl env q args = let
  nest     = modName q
  bindNm   = unQName q
  noInline = Left <$> AppF (Var (VLetBind q)) args
  (bruijnN , unstructuredArgs , repackedArgs , argShapes) = destructureArgs args
  in -- d_ args $ d_ argShapes $ d_ repackedArgs $ d_ unstructuredArgs $ d_ "" $
  use letBinds >>= \lb -> (lb `MV.read` nest) >>= \bindVec -> MV.read bindVec bindNm >>= \case
  BindOK o _free expr@(Core inlineF _ty) | any (/= ShapeNone) argShapes -> case bindSpecs o M.!? argShapes of
    Just cachedSpec -> pure $ AppF (Left cachedSpec) (Left <$> unstructuredArgs)
    Nothing -> if all (\case { ShapeNone -> True ; _ -> False }) argShapes then pure noInline else do
      let recGuard = LetSpec q argShapes
      MV.modify bindVec (\(BindOK (OptBind oLvl oSpecs) free _t)
        -> BindOK (OptBind oLvl (M.insert argShapes recGuard oSpecs)) free expr) bindNm

      -- ! repackedArgs are at lvl, inlineF is at (lvl + bruijnN)
      -- fully simplify the specialised partial application (if it recurses then this spec is extremely valuable)
      let rawAbs = BruijnAbs bruijnN (App inlineF repackedArgs)
      specFn <- simpleTerm' lvl env rawAbs -- TODO if repackedArgs contains debruijns this may break
      -- (fst env , TSub (mkBruijnArgSubs lvl (V.length (fst env))) (bruijnN + lvl) <$> repackedArgs) rawAbs
      when debug_fuse $ do
        traceM $ "raw spec " <> show bindNm <> " " <> show argShapes <> "\n => " <> prettyTermRaw rawAbs <> "\n"
        traceM $ "simple spec " <> prettyTermRaw specFn <> "\n"

      MV.modify bindVec (\(BindOK (OptBind oLvl oSpecs) free _t)
        -> BindOK (OptBind oLvl (M.insert argShapes specFn oSpecs)) free expr) bindNm

      let fn = if lvl == 0 then specFn else recGuard
      pure $ Left <$> if null unstructuredArgs then project fn else AppF fn unstructuredArgs
  _ -> pure noInline
