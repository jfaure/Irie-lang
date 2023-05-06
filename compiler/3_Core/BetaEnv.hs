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

-- TODO β-optimal; precompute calculations involving env ; trim env?
-- # abs
--   +lvl -> inc subbed in vbruijns later
-- # app abs -> setup β-env
-- # insert fn -> possibly re-app

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

  -- simplifying a raw abs will produce bruijn arg subs
  -- ?? Need to force but also may need to re-fuse in different β-env later
  -- simplify then check trailingArgs only if necessary
--f -> simpleTerm' lvl (argEnv , mempty) term >>= \g -> case getBruijnAbs g of
--  Just (n , body) -> fuseApp n (Forced eLen lvl $ did_ body) trailingArgs
--  _ -> pure $ AppF (Left g) (unSub <$> trailingArgs)

mkBruijnArgSubs l n = V.generate n (\i -> TSub mempty {- doesn't matter -} l (VBruijnLevel (l - i - 1)))

-- ! current term and trailingArgs have different envs
fuse :: forall s. Seed -> SimplifierEnv s (TermF (Either Term Seed))
fuse (lvl , env@(argEnv , trailingArgs) , term) = let
  eLen = V.length argEnv
  unSub (TSub prevArgEnv prevLvl arg) | prevLvl == lvl = Right (lvl , (prevArgEnv , mempty) , arg)
 -- unSub (TSub prevArgEnv prevLvl arg) = traceShow (prevLvl , lvl) $ Right (lvl , (prevArgEnv , mempty) , arg)
  in --trace (show term <> "\nenv: " <> show argEnv <> "\n---\n" :: Text) $
  case term of
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
  Var (VLetBind q) | lvl == 0 -> use letBinds >>= \lb -> (lb `MV.read` (modName q))
    >>= \bindVec -> MV.read bindVec (unQName q) >>= \case
      BindOK _ (nL , letCapture) (Core inlineF _ty) -> let
        env' = (V.drop (V.length argEnv - nL) argEnv , trailingArgs)
        in fuse (lvl , env' , inlineF)
      x -> error $ show x

  Label l ars -> pure $ LabelF l
    $  (Right . (lvl , (argEnv , mempty) ,) <$> ars)
    <> (unSub <$> trailingArgs)

  -- ! Needs to pull out the seed immediately, but perhaps fuse multiple case-case
  CaseB scrut retT branches d -> simpleTerm' lvl (argEnv , []) {-scrut has no trailingArgsenv-} scrut
    >>= fuseCase retT branches d where
   idEnv = mkBruijnArgSubs lvl (V.length $ fst env) -- TODO check the trailingArgs!
-- fuseCase :: Type -> BSM Term -> Maybe Term -> Term -> SimplifierEnv s (TermF (Either Term Seed))
   fuseCase retT branches d = \case
  -- case-label
      Label l params -> case branches BSM.!? qName2Key l <|> d of
        Just body | null params -> fuse (lvl , env , body)
        -- v params are already β-d at this lvl, so give them idSubs!
        Just body -> fuse (lvl , (argEnv , (params <&> TSub idEnv lvl) <> trailingArgs) , body)
        Nothing -> error $ "panic: no label: " <> show l <> " : " <> show params <> "\n; " <> show (BSM.keys branches)
  -- case-case: push/copy outer case to each branch, then the inner case output fuses with outer case labels
  -- Everything is already β-reduced except branches and d
  -- ! these are label => Fn pairs
  -- TODO (?) need to inc args within the pushed case (normally case-Abs are distinct, but now we're stacking them)
--    CaseB innerScrut ty2 innerBranches innerDefault -> let
--      pushCase = \case -- this will produce a case-label for each branch
--        BruijnAbs n innerOutput -> BruijnAbs n (CaseB innerOutput retT branches d) -- A case-label
--        BruijnAbsTyped{} -> _
--        innerOutput@Label{} -> CaseB innerOutput retT branches d
--        innerOutput -> _
--    --pushCase innerOutput = did_ $ CaseB innerOutput retT branches d -- A case-label
--      optBranches = pushCase <$> innerBranches
--      optD        = pushCase <$> innerDefault
--      in fuseCase ty2 optBranches optD innerScrut -- retry one-step fusion without re-βreducing the scrut

      opaqueScrut -> pure $ CaseBF (Left opaqueScrut) retT (Right . (lvl,env,) <$> branches)
                                                           (Right . (lvl,env,) <$> d)

  -- Try before and after forcing the scrut
  -- TODO other lenses ; trailingArgs
  TTLens scrut [f] LensGet | null trailingArgs -> simpleTerm' lvl env scrut >>= \case
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

inferBlock lets go = do
  nest <- letNest <<%= (1+)
  v <- use letBinds >>= \lvl -> V.thaw (snd <$> lets) >>= \v -> MV.write lvl nest v $> v
  go v <* (letNest %= \x -> x - 1) -- <* traceM "decBlock" 

-- TODO how to avoid duplicate simplifications?
-- ie. iff no VBruijns to solve: isEnvEmpty
simpleBind lvl env b = case b of
  BindOK (OptBind optLvl specs) free (Core t ty) -> if isEnvEmpty env && optLvl /= 0 then pure b else do
    newT <- simpleTerm' lvl env t
    pure (BindOK (OptBind ({-optLvl +-} 1) specs) free (Core newT ty))
  x -> error $ show x

simpleTerm' :: Int -> Env -> Term -> SimplifierEnv s Term
simpleTerm' lvl env t = hypoM primF fuse (lvl , env , t)
simpleTerm t = do
  letBinds' <- MV.new 64 -- max let-depth
  simpleTerm' 0 (mempty , mempty) t `evalStateT` FEnv letBinds' 0

simpleExpr :: Expr -> ST s Expr
simpleExpr (Core t ty) = simpleTerm t <&> \t -> Core t ty
simpleExpr _ = pure PoisonExpr

primF :: TermF Term -> Term
primF = \case
  AppF (Instr i) args -> simpleInstr i args
  AppF (App g args) brgs -> primF (AppF g (args <> brgs))
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

{-
specApp :: forall s. Lvl -> Env -> QName -> [Term] -> SimplifierEnv s (TermF (Either Term Seed))
specApp lvl env q args = let
  nest = modName q ; bindNm  = unQName q
  noInline = AppF (Left $ Var (VLetBind q)) (Right . (lvl,env,) <$> args)
  (bruijnN , unstructuredArgs , repackedArgs , argShapes) = destructureArgs args
  in -- d_ args $ d_ argShapes $ d_ repackedArgs $ d_ unstructuredArgs $ d_ "" $
  use letBinds >>= \lb -> (lb `MV.read` nest) >>= \bindVec -> MV.read bindVec bindNm >>= \case
  BindOK o _free expr@(Core inlineF _ty) | any (/= ShapeNone) argShapes ->
    case bindSpecs o M.!? argShapes of
    Just cachedSpec -> pure $ AppF (Left cachedSpec) (Right . (lvl,env,) <$> unstructuredArgs)
    Nothing -> if all (\case { ShapeNone -> True ; _ -> False }) argShapes then pure noInline else do
      let recGuard = LetSpec q argShapes
      MV.modify bindVec (\(BindOK (OptBind oLvl oSpecs) free _t)
        -> BindOK (OptBind oLvl (M.insert argShapes recGuard oSpecs)) free expr) bindNm

      -- ! repackedArgs are at lvl, inlineF is at (lvl + bruijnN), so we need to patch the ars
      -- ideally we could skip this traversal of the args with some level manipulation (maybe a new Sub)
--    ars <- simpleTerm' (lvl + bruijnN) env `mapM` repackedArgs
--    let raw = App inlineF ars ; rawAbs = if bruijnN == 0 then raw else BruijnAbs bruijnN emptyBitSet raw
--    specFn <- simpleTerm' lvl env rawAbs

      -- fully simplify the specialised partial application (if it recurses then the spec is extremely valuable)
      let rawAbs = BruijnAbs bruijnN (App inlineF repackedArgs)
      specFn <- simpleTerm' lvl env rawAbs
      when debug_fuse $ do
        traceM $ "raw spec " <> show bindNm <> " " <> show argShapes <> "\n => " <> prettyTermRaw rawAbs <> "\n"
        traceM $ "simple spec " <> prettyTermRaw specFn <> "\n"

      MV.modify bindVec (\(BindOK (OptBind oLvl oSpecs) free _t)
        -> BindOK (OptBind oLvl (M.insert argShapes specFn oSpecs)) free expr) bindNm

      let fn = if lvl == 0 then specFn else recGuard
      if null unstructuredArgs then pure $ Left <$> project fn else fuse (lvl , env , App fn unstructuredArgs)
  _ -> pure noInline
-}
