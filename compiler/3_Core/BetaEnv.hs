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
data Sub = TSub Int Lvl Term deriving Show -- eLen lvl term
type Env = (V.Vector Sub , [Sub]) -- [(Int , Term)]) -- length of argEnv (needs to remain consistent across paps
isEnvEmpty (subs , tArgs) = V.null subs
type Seed = (Lvl , Env , Int , Term) -- expected eLen may be < envlen since tsubs eLen can increase

-- TODO β-optimal; precomupte calculations involving env ; trim env?
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

--  ! Can't instantly simplify args to an App in case f contains more bruijnAbs. Also VBruijns may need relevelling
--  TODO this may duplicate work if simplified twice at the same lvl; counting on dup nodes + β-optimality to fix this

  -- simplifying a raw abs will produce bruijn arg subs
  -- ?? Need to force but also may need to re-fuse in different β-env later
  -- simplify then check trailingArgs only if necessary
--f -> simpleTerm' lvl (argEnv , mempty) term >>= \g -> case getBruijnAbs g of
--  Just (n , body) -> fuseApp n (Forced eLen lvl $ did_ body) trailingArgs
--  _ -> pure $ AppF (Left g) (unSub <$> trailingArgs)

mkBruijnArgSubs l n = V.generate n (\i -> TSub 5000 {- doesn't matter -} l (VBruijnLevel (l - i - 1)))

-- ! current term and trailingArgs have different envs
fuse :: forall s. Seed -> SimplifierEnv s (TermF (Either Term Seed))
fuse (lvl , env@(argEnv , trailingArgs) , atLen , term) = let
 eLen = V.length argEnv
 unSub (TSub prevELen prevLvl arg) | prevLvl == lvl = Right (lvl , (argEnv , mempty) , prevELen , arg)
 in --trace (show term <> "\nenv: " <> show argEnv <> "\n---\n" :: Text) $
 case term of
  App f args -> fuse (lvl , (argEnv , (TSub atLen lvl <$> args) <> trailingArgs) , atLen , f)

  abs | Just (n , body) <- getBruijnAbs abs -> if null trailingArgs
    then case getBruijnAbs body of -- not β-reducing => spawn bruijn arg subs
      Just (m , b2) -> fuse (lvl , env , atLen , BruijnAbs (m + n) b2)
      _ -> pure $ BruijnAbsF n (Right (lvl + n , (mkBruijnArgSubs (lvl + n) n <> argEnv , mempty) , atLen + n , body))
    else claimArgs n body trailingArgs atLen where
      claimArgs :: Int -> Term -> [Sub] -> Int -> SimplifierEnv s (TermF (Either Term Seed))
      claimArgs n body trailingArgs atLen = let
         -- ! if body β-reduces into an abs then that abs skips these claimed args
        (ourArgs , remArgs) = splitAt n trailingArgs
        l = length ourArgs
        --overAtLen f (TSub al pl arg) = TSub (f al) pl arg
        -- patchAbs: captured freevar vs new bruijns => iff arg is a bruijnAbs then atLen skips claimedArgs
        -- captured = \x => ((\b => b) x)             -- do nothing, x is passed down
        -- subAbs   = (\f => f) (\x y => add y 2) 3   -- (\x y => _) needs to skip 'f' in env
        patchAbs l tsub@(TSub al pl arg) = case getBruijnAbs arg of
          -- TODO is this robust accross multiple functions?
          Just{} -> TSub (al + length remArgs) pl arg -- + length of remArgs instead of + length of ourArgs
          _      -> tsub
        in case compare l n of
          EQ -> let nextEnv = V.reverse (V.fromList ourArgs) <&> patchAbs l
            in fuse (lvl , (nextEnv <> argEnv , remArgs) , atLen + V.length nextEnv , body)
          LT -> claimArgs l (BruijnAbs (n - l) body) trailingArgs atLen
          GT -> error "impossible"

  VBruijnLevel l -> pure $ let v = lvl - l - 1
    in if null trailingArgs then VBruijnF v else AppF (Left (VBruijn v)) (unSub <$> trailingArgs)

  -- env contains raw args to simplify, at the new lvl for any bruijns subbed in
  -- This duplicates work if simplifying the same arg twice at the same lvl - need β-optimality
  VBruijn j -> let i = j + eLen - atLen in if i >= eLen then error $ show (i , env) else
    argEnv V.! i & \(TSub prevLen prevLvl argTerm) -> let --if lvl /= prevLvl then _ else let
      in --d_ (i , argTerm , argEnv , trailingArgs) $
        fuse (lvl , (argEnv , trailingArgs) , prevLen , argTerm)

  Var (VLetBind q) | lvl == 0 -> inlineLetBind q >>= \fn -> fuse (lvl , env , atLen , fn)

  Label l ars -> pure $ LabelF l
    $  (Right . (lvl , (argEnv , mempty) , atLen ,) <$> ars)
    <> (unSub <$> trailingArgs)

  CaseB scrut retT branches d -> simpleTerm' lvl env atLen scrut >>= \case -- Need to pull out the seed immediately
-- case-label
    Label l params -> case branches BSM.!? qName2Key l <|> d of
      Just body | null params -> fuse (lvl , env , atLen , body)
      Just body -> fuse (lvl , env , atLen , App body (Forced atLen lvl <$> params)) -- params are already β-d at lvl
      Nothing -> error $ "panic: no label: " <> show l <> " : " <> show params <> "\n; " <> show (BSM.keys branches)
-- case-case: push/copy outer case into each branch, then the inner case fuses with outer case output labels
-- Everything is forced already except branches and d
    CaseB innerScrut ty2 innerBranches innerDefault -> let
      pushCase innerBody = CaseB (Forced atLen lvl innerBody) retT branches d
      optBranches = pushCase <$> innerBranches
      optD        = pushCase <$> innerDefault
      in fuse (lvl , env , atLen , CaseB (Forced atLen lvl innerScrut) ty2 optBranches optD)
    opaqueScrut -> pure $ CaseBF (Left opaqueScrut) retT (Right . (lvl,env,atLen,) <$> branches)
                                                         (Right . (lvl,env,atLen,) <$> d)

  -- TODO try before and after forcing the scrut
  -- TODO trailingArgs
--TTLens scrut [f] LensGet -> simpleTerm' lvl env scrut >>= \case
--  LetBlock l -> case V.find ((==f) . iName . fst) l of
--    Just x -> pure $ Left <$> (\(Core t _ty) -> project t) (naiveExpr (snd x))
--  opaque -> pure $ TTLensF (Left opaque) [f] LensGet

  LetBlock lets -> unless (null trailingArgs) (error "") *>
    inferBlock lets (\_ -> LetBlockF <$> lets `forM` \(lm , bind) -> (lm ,)
      <$> simpleBind lvl (argEnv , mempty) atLen bind)
  LetBinds lets inE -> inferBlock lets $ \v -> do
    newLets <- lets `forM` \(lm , bind) -> (lm ,) <$> simpleBind lvl (argEnv , mempty) atLen bind
    newInE  <- simpleTerm' lvl env atLen inE
    pure $ if lvl == 0 then Left <$> project newInE else LetBindsF newLets (Left newInE)

  -- used for args that are pre-β-d by case-fusion
--Forced{} -> _
  Forced prevELen prevLvl t -> if
    | prevLvl == lvl || prevLvl == 0 -> when (prevELen /= atLen) (error "") *> pure (
      if null trailingArgs then Left <$> project t else AppF (Left t) (unSub <$> trailingArgs))
--  | prevLvl < lvl -> trace (show prevLvl <> " < " <> show lvl :: Text)
--      (fuse (lvl , (did_ $ mkBruijnArgSubs lvl prevLvl , mempty , 0) , t))
  x -> pure $ if null trailingArgs
    then Right . (lvl , env , atLen ,) <$> project x
    else AppF (Right (lvl , (argEnv , mempty) , atLen , x)) (unSub <$> trailingArgs)

inferBlock lets go = do
  nest <- letNest <<%= (1+)
  v <- use letBinds >>= \lvl -> V.thaw (snd <$> lets) >>= \v -> MV.write lvl nest v $> v
  go v <* (letNest %= \x -> x - 1) -- <* traceM "decBlock" 

-- TODO how to avoid duplicate simplifications?
-- ie. iff no VBruijns to solve: isEnvEmpty
simpleBind lvl env eLen b = case b of
  BindOK (OptBind optLvl specs) free (Core t ty) -> if isEnvEmpty env && optLvl /= 0 then pure b else do
    newT <- simpleTerm' lvl env eLen t
    pure (BindOK (OptBind ({-optLvl +-} 1) specs) free (Core newT ty))
  x -> error $ show x

simpleTerm' :: Int -> Env -> Int -> Term -> SimplifierEnv s Term
simpleTerm' lvl env eLen t = hypoM primF fuse (lvl , env , eLen , t)
simpleTerm t = do
  letBinds' <- MV.new 64 -- max let-depth
  simpleTerm' 0 (mempty , mempty) 0 t `evalStateT` FEnv letBinds' 0

simpleExpr :: Expr -> ST s Expr
simpleExpr (Core t ty) = simpleTerm t <&> \t -> Core t ty
simpleExpr _ = pure PoisonExpr

inlineLetBind q = use letBinds >>= \lb -> (lb `MV.read` (modName q))
  >>= \bindVec -> MV.read bindVec (unQName q) <&> \case
    BindOK _ _free (Core inlineF _ty) -> inlineF
    x -> error $ show x

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
