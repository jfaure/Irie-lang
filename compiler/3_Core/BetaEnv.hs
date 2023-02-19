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

-- TODO β-optimal; precomupte calculations involving free-vars
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

simplifiable = \case
  VBruijn{} -> True
  App (VBruijn{}) _ -> True
  App (Var VLetBind{}) _ -> True
  Var (VLetBind q)       -> True
  _ -> False

type Lvl = Int
type Env = (V.Vector Sub , [Term])
type Seed = (Int , Env , Term)
data Sub = TSub Int Lvl Term deriving Show

-- # abs
--   +lvl -> inc subbed in vbruijns later
-- # app abs -> setup β-env
-- # insert fn -> possibly re-app

fuse :: forall s. Seed -> SimplifierEnv s (TermF (Either Term Seed))
fuse (lvl , env@(argEnv , trailingArgs) , term) = --trace (show term <> "\nenv: " <> show argEnv <> "\n---\n" :: Text) $
 if not (null trailingArgs)
 then case term of
  Label l ars -> pure $ LabelF l (Right . (lvl , (argEnv , mempty) , ) <$> (ars <> trailingArgs))
--  ! Can't simplify the args yet in case f contains more bruijnAbs, so delay until they are simplified in context
--  TODO this may duplicate work if simplified twice at the same lvl; counting on dup nodes + β-optimality to fix this
  f | Just (n , body) <- getBruijnAbs f , (ourArgs , remArgs) <- splitAt n trailingArgs , l <- length ourArgs ->
    case compare n l of
      GT -> fuse (lvl , (argEnv , ourArgs) , BruijnAbs (n - l) 0 (BruijnAbs l 0 body)) -- let abs case handle PAP
      LT -> error $ show (n , length ourArgs)
      EQ -> let nextEnv = V.reverse (V.fromList $ TSub (V.length argEnv) lvl <$> ourArgs)
        in fuse (lvl , (nextEnv <> argEnv , remArgs) , body) -- TODO remArgs eLen will be off by n !

  -- Retry app if f simplifies. TODO track if simplification happened
--f | lvl == 0 && simplifiable f -> simpleTerm' lvl (argEnv , mempty) term >>= \fn -> fuse (lvl , env , fn)
  Var (VLetBind q) | lvl == 0 -> inlineLetBind q >>= \fn -> fuse (lvl , env , fn)
  VBruijn i | lvl == 0 -> simpleTerm' lvl (argEnv , mempty) term >>= \case
--  VBruijn j -> _ -- didn't simplify?
    fn        -> fuse (lvl , env , fn)
  App{} | lvl == 0 -> simpleTerm' lvl (argEnv , mempty) term >>= \fn -> fuse (lvl , env , fn) -- what if no simplification?!
  -- TODO check if simplification happened

  f -> pure $ AppF (Right (lvl , (argEnv , mempty) , f))
                   (Right . (lvl , (argEnv , mempty) ,) <$> trailingArgs)
 else let eLen = V.length argEnv in case term of
  VBruijnLevel l -> pure $ VBruijnF (lvl - l - 1)
  -- need to re-lvl any bruijns subbed in
  VBruijn i -> if i >= eLen then error $ show (i , env) else
    -- This may duplicate work if copying args at the same lvl - need β-optimality
    argEnv V.! i & \(TSub prevELen prevLvl argTerm) -> let --if lvl /= prevLvl then _ else let
--    prevEnv = V.drop (eLen - prevELen) argEnv -- <&> \(TSub pl p t) -> TSub pl p (Forced lvl t)
      newEnv = V.drop (eLen - prevELen) argEnv -- takeEnd prevELen
      in -- d_ (lvl , prevLvl , prevELen , eLen , argTerm , argEnv) $
--      d_ (argTerm , env) $ 
        d_ (i , prevELen , eLen , argTerm , env) $
        fuse (lvl , (newEnv , mempty) , argTerm)

  abs | Just (n , body) <- getBruijnAbs abs -> case getBruijnAbs body of
    Just (m , b2) -> fuse (lvl , env , BruijnAbs (m + n) 0 b2)
    _ -> let
      args = V.generate n (\i -> TSub 0 {- doesn't matter -} (lvl + n) (VBruijnLevel (lvl + n - i - 1)))
      in pure $ BruijnAbsF n 0 (Right (lvl + n , (args <> argEnv , mempty) , body))

--App f args@[_]   -> fuse (lvl , (argEnv , args) , f)
--App f (a:args)   -> fuse (lvl , env , App (App f [a]) args)
  App f args   -> fuse (lvl , (argEnv , args) , f)
--Label l args -> fuse (lvl , (argEnv , args) , Label l [])

  CaseB scrut retT branches d -> simpleTerm' lvl env scrut >>= \case -- Need to pull out the seed immediately
-- case-label
    Label l params -> case branches BSM.!? qName2Key l <|> d of
      Just body | null params -> fuse (lvl , env , body)
      -- !! WARNING params are already β-d
      Just body -> fuse (lvl , env , App body (Forced lvl <$> params))
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

  Forced prevLvl t -> if prevLvl /= lvl then error "" else pure $ Left <$> project t
  x -> pure $ Right . (lvl , env ,) <$> project x

inferBlock lets go = do
  nest <- letNest <<%= (1+)
  v <- use letBinds >>= \lvl -> V.thaw (snd <$> lets) >>= \v -> MV.write lvl nest v $> v
  go v <* (letNest %= \x -> x - 1) -- <* traceM "decBlock" 

simpleTerm' lvl env t = hypoM (pure . primF) fuse (lvl , env , t)
simpleTerm t = do
  letBinds' <- MV.new 64 -- max let-depth
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
