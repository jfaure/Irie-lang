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

-- It is critical to fully traverse terms, otherwise stale VBruijns may be left over

debug_fuse = True

data FEnv s = FEnv
 { _letBinds :: MV.MVector s (MV.MVector s Bind)
 , _letNest  :: Int
 }; makeLenses ''FEnv
type SimplifierEnv s = StateT (FEnv s) (ST s)

getBruijnAbs = \case
  BruijnAbs n _ body -> Just (n , body)
  BruijnAbsTyped n _ body _ _ -> Just (n , body)
  _ -> Nothing

type Lvl = Int
type Env = V.Vector Sub
type Seed = (Int , Env , Term)
data Sub
 = BruijnSub Lvl Int -- can skip a re-traversal (although it would be very cheap anyway)
 | TermSub   Lvl Term deriving Show

idEnv l e = V.generate (V.length e) (\i -> BruijnSub l i)

-- * weaken: apply a lambda => add arg to env => if arg contains VBruijns, add their index
-- * quote:  wrap a lambda over a term => recalculate bruijn indices underneath
fuse :: forall s. Seed -> SimplifierEnv s (TermF (Either Term Seed))
fuse (lvl , env , term) = case term of
  abs | Just (n , body) <- getBruijnAbs abs , Just (m , b2) <- getBruijnAbs body
    -> fuse (lvl , env , BruijnAbs (n + m) 0 b2)
  App (App g ars)   args -> fuse (lvl , env , App g (ars <> args))
  App (Label l ars) args -> fuse (lvl , env , Label l (ars <> args))

  CaseB scrut retT branches d -> simpleTerm' lvl env scrut >>= \case -- Need to pull out the seed immediately
-- case-label
    Label l params -> case (branches BSM.!? qName2Key l) <|> d of
      Just body | null params -> fuse (lvl , env , body)
      -- !! WARNING params are already β-d , but more β-s needed now
      Just body -> fuse (lvl , env , App body params)
      Nothing -> error $ "panic: no label: " <> show l <> " : " <> show params <> "\n; " <> show (BSM.keys branches)
-- case-case: push/copy outer case into each branch, then the inner case fuses with outer case output labels
    CaseB innerScrut ty2 innerBranches innerDefault -> let
      pushCase innerBody = CaseB innerBody retT branches d
      optBranches = pushCase <$> innerBranches
      optD        = pushCase <$> innerDefault
      in fuse (lvl , env , CaseB innerScrut ty2 optBranches optD)
    opaqueScrut -> pure $ CaseBF (Left opaqueScrut) retT (Right . (lvl,env,) <$> branches) (Right . (lvl,env,) <$> d)

  LetBlock lets -> inferBlock lets $ \_ -> LetBlockF <$> lets `forM` \(lm , bind) -> (lm ,) <$> simpleBind lvl env bind
  LetBinds lets inE -> inferBlock lets $ \v -> do
    newLets <- lets `forM` \(lm , bind) -> (lm ,) <$> simpleBind lvl env bind
--  newLets <- V.indexed lets `forM` \(i , (lm , bind)) -> simpleBind lvl env bind >>= \b -> (lm , b) <$ MV.write v i b
    newInE  <- simpleTerm' lvl env inE
    pure $ if lvl == 0 then Left <$> project newInE else LetBindsF newLets (Left newInE)

  -- Bruijn manipulations: Any contained debruijns must be diffed with their lvl change
  VBruijn i -> if i >= V.length env then error $ show (i , env) else (env V.! i) & \case
    BruijnSub prevLvl i -> pure $ VBruijnF (lvl - prevLvl + i)
    TermSub prevLvl argTerm -> -- if prevLvl == lvl then pure $ Left <$> project argTerm
--    {-else-} fuse (lvl , V.generate prevLvl (\i -> BruijnSub lvl i) , argTerm) -- adjust deBruijn levels
      fuse (lvl , V.drop lvl env , argTerm) -- ?!
  abs | Just (n , body) <- getBruijnAbs abs -> let args = V.generate n (\i -> BruijnSub (lvl + n) i)
    in pure $ BruijnAbsF n 0 $ Right (lvl + n , args <> env , body)

  -- β-reduction & let-bind substitutions may generate more fusion opportunities
  -- TODO avoid retraversal of the args at this lvl
  App (VBruijn i) args | lvl == 0 -> simpleTerm' lvl env (VBruijn i) >>= \case
    VBruijn j -> pure $ AppF (Left (VBruijn j)) (Right . (lvl,env,) <$> args)
    f -> (simpleTerm' lvl env `mapM` args) >>= \ars -> fuse (lvl , env , App f ars)

  App (Var (VLetBind q)) args | lvl == 0 -> inlineLetBind q >>= \inlineF ->
    (simpleTerm' lvl env `mapM` args) >>= \ars -> fuse (lvl , env , App inlineF ars)
--  fuse (lvl , env , App inlineF args)

--App (Var (VLetBind q)) args -> specApp lvl env q args

  App f rawArgs
    | Just (n , body) <- getBruijnAbs f , (ourArgs , remArgs) <- splitAt n rawArgs
      -> mapM (simpleTerm' lvl env) ourArgs >>= \ars -> let
      l      = length rawArgs
--    argEnv = V.reverse (V.fromList $ zipWith TermSub [lvl+1..] ars)
      argEnv = V.reverse (V.fromList $ TermSub lvl <$> ars)
      in if
      | n == l -> fuse (lvl , argEnv <> env , body)
      | n < l  -> simpleTerm' lvl (argEnv <> env) body >>= \g ->
--      mapM (simpleTerm' lvl env) remArgs >>= \r ->
        fuse (lvl , env , App g remArgs)
      | n < l  -> simpleTerm' lvl (argEnv <> env) body >>= \g ->
--      mapM (simpleTerm' lvl env) remArgs >>= \r ->
        fuse (lvl , env , App g remArgs)

      | True {-n > l-} -> trace (prettyTermRaw (App f ars)) $
--      simpleTerm' lvl env f >>= \g -> fuse (lvl , env , App (Forced lvl g) rawArgs)
        fuse (lvl , env , BruijnAbs l 0 (App f (rawArgs ++ [VBruijn i | i <- [n-l-1 , n-l-2 .. 0]])))
--      fuse (lvl , env , BruijnAbs l 0 (App f (rawArgs ++ [VBruijn i | i <- [n-l-1 , n-l-2 .. 0]])))
--    | n > l  -> fuse (lvl , argEnv <> env , BruijnAbs (n - l) 0 body)

  Forced prevLvl t -> trace (prettyTermRaw t) $ if prevLvl /= lvl then error "" else pure $ Left <$> project t
  x -> pure $ Right . (lvl , env ,) <$> project x

inferBlock lets go = do
  nest <- letNest <<%= (1+)
  v <- use letBinds >>= \lvl -> V.thaw (snd <$> lets) >>= \v -> MV.write lvl nest v $> v
  go v <* (letNest %= \x -> x - 1) -- <* traceM "decBlock" 

simpleTerm' lvl env t = hypoM (pure . primF) fuse (lvl , env , t) -- cata primF $ apo fuse (lvl , env , t)
simpleTerm t = do
  letBinds' <- MV.new 16
  simpleTerm' 0 mempty t `evalStateT` FEnv letBinds' 0

simpleExpr (Core t ty) = simpleTerm t <&> \t -> Core t ty
simpleExpr _ = pure PoisonExpr

simpleBind lvl env b = case b of
  BindOK (OptBind optLvl specs) (Core t ty) -> if optLvl /= 0 then pure b else do
    newT <- simpleTerm' lvl env t
    pure (BindOK (OptBind (optLvl + 1) specs) (Core newT ty))
  x -> error $ show x

inlineLetBind q = use letBinds >>= \lb -> (lb `MV.read` (modName q))
  >>= \bindVec -> MV.read bindVec (unQName q) <&> \case
    BindOK _ (Core inlineF _ty) -> inlineF
    x -> error $ show x

-- * compute instructions
-- ? track free vars for deBruijn abstractions
-- ? count QTT

primF :: TermF Term -> Term
primF = \case
  AppF (Instr i) args -> simpleInstr i args
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
  nest = modName q ; bindNm  = unQName q
  noInline = AppF (Left $ Var (VLetBind q)) (Right . (lvl,env,) <$> args)
  (bruijnN , unstructuredArgs , repackedArgs , argShapes) = destructureArgs args
  in -- d_ args $ d_ argShapes $ d_ repackedArgs $ d_ unstructuredArgs $ d_ "" $
  use letBinds >>= \lb -> (lb `MV.read` nest) >>= \bindVec -> MV.read bindVec bindNm >>= \case
  BindOK o expr@(Core inlineF _ty) | any (/= ShapeNone) argShapes ->
    case bindSpecs o M.!? argShapes of
    Just cachedSpec -> pure $ AppF (Left cachedSpec) (Right . (lvl,env,) <$> unstructuredArgs)
    Nothing -> if all (\case { ShapeNone -> True ; _ -> False }) argShapes then pure noInline else do
      let recGuard = LetSpec q argShapes
      MV.modify bindVec (\(BindOK (OptBind oLvl oSpecs) _t)
        -> BindOK (OptBind oLvl (M.insert argShapes recGuard oSpecs)) expr) bindNm

      -- ! repackedArgs are at lvl, inlineF is at (lvl + bruijnN), so we need to patch the ars
      -- ideally we could skip this traversal of the args with some level manipulation (maybe a new Sub)
--    ars <- simpleTerm' (lvl + bruijnN) env `mapM` repackedArgs
--    let raw = App inlineF ars ; rawAbs = if bruijnN == 0 then raw else BruijnAbs bruijnN emptyBitSet raw
--    specFn <- simpleTerm' lvl env rawAbs

      -- fully simplify the specialised partial application (if it recurses then the spec is extremely valuable)
      let rawAbs = BruijnAbs bruijnN 0 (App inlineF repackedArgs)
      specFn <- simpleTerm' lvl env rawAbs
      when debug_fuse $ do
        traceM $ "raw spec " <> show bindNm <> " " <> show argShapes <> "\n => " <> prettyTermRaw rawAbs <> "\n"
        traceM $ "simple spec " <> prettyTermRaw specFn <> "\n"

      MV.modify bindVec (\(BindOK (OptBind oLvl oSpecs) _t)
        -> BindOK (OptBind oLvl (M.insert argShapes specFn oSpecs)) expr) bindNm

      let fn = if lvl == 0 then specFn else recGuard
      if null unstructuredArgs then pure $ Left <$> project fn else fuse (lvl , env , App fn unstructuredArgs)
  _ -> pure noInline
