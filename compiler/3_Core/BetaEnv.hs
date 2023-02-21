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

-- hacky equality test to check if a term simplified
deriving instance Eq (TermF Int)
deriving instance Eq VName
instance Eq BiCast where (==)  = \a b -> True
instance Eq LetMeta where (==) = \a b -> True
instance Eq Bind where (==)    = \a b -> True
instance Eq LensOp where (==)  = \a b -> True

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
type Env = (V.Vector Sub , [(Int , Term)]) -- length of argEnv (needs to remain consistent across paps
isEnvEmpty (subs , tArgs) = V.null subs
type Seed = (Int , Env , Term)
data Sub = TSub Int Lvl Term deriving Show

-- # abs
--   +lvl -> inc subbed in vbruijns later
-- # app abs -> setup β-env
-- # insert fn -> possibly re-app

--  ! Can't instantly simplify args to an App in case f contains more bruijnAbs. Also VBruijns may need relevelling
--  TODO this may duplicate work if simplified twice at the same lvl; counting on dup nodes + β-optimality to fix this

mkBruijnArgSubs l n = V.generate n (\i -> TSub 0 {- doesn't matter -} l (VBruijnLevel (l - i - 1)))

fuse :: forall s. Seed -> SimplifierEnv s (TermF (Either Term Seed))
fuse (lvl , env@(argEnv , trailingArgs) , term) = let eLen = V.length argEnv
 in --trace (show term <> "\nenv: " <> show argEnv <> "\n---\n" :: Text) $
 if not (null trailingArgs)
 then let
  fuseApp n body trailingArgs = let
    (ourArgs , remArgs) = splitAt n trailingArgs
    l = length ourArgs
    in if
      | l == n -> let nextEnv = V.reverse (V.fromList $ (\(tL , arg) -> TSub tL lvl arg) <$> ourArgs)
        in fuse (lvl , (nextEnv <> argEnv , remArgs) , body) -- TODO remArgs eLen will be off by n !
      | l < n  -> fuseApp l (BruijnAbs (n - l) 0 body) trailingArgs
      | True -> error "impossible"
  in case term of
  Label l ars -> pure $ LabelF l (Right . (lvl , (argEnv , mempty) ,) <$> (ars <> map snd trailingArgs))
  f | Just (n , body) <- getBruijnAbs f -> fuseApp n body trailingArgs

  -- simplifying a raw abs will produce bruijn arg subs
  f -> simpleTerm' lvl (argEnv , mempty) term >>= \g -> case getBruijnAbs g of
    Just (n , body) -> fuseApp n body trailingArgs
    _ -> pure $ AppF (Left g) $ (Right . (lvl , (argEnv , mempty) ,) . snd) <$> trailingArgs

 else case term of
  VBruijnLevel l -> pure $ VBruijnF (lvl - l - 1)

  VBruijn i -> if i >= eLen then error $ show (i , env) else
    -- then env contains raw args to simplify, at the new lvl for any bruijns subbed in
    -- This duplicates work if simplifying the same arg twice at the same lvl - need β-optimality
    argEnv V.! i & \(TSub prevELen prevLvl argTerm) -> let --if lvl /= prevLvl then _ else let
      newEnv = V.drop (eLen - prevELen) argEnv -- takeEnd prevELen
      in fuse (lvl , (newEnv , mempty) , argTerm)

  abs | Just (n , body) <- getBruijnAbs abs -> case getBruijnAbs body of
    Just (m , b2) -> fuse (lvl , env , BruijnAbs (m + n) 0 b2)
    _ -> pure $ BruijnAbsF n 0 (Right (lvl + n , (mkBruijnArgSubs (lvl + n) n <> argEnv , mempty) , body))

--App (App g gs) args -> fuse (lvl , (argEnv , (gs <> args) , V.length argEnv) , g)
  App f args -> fuse (lvl , (argEnv , (V.length argEnv ,) <$> args) , f)

  -- This will spoil free-var indexes, so may as well void the env anyway
  Var (VLetBind q) | lvl == 0 -> inlineLetBind q >>= \fn -> fuse (lvl , mempty , fn)

  CaseB scrut retT branches d -> simpleTerm' lvl env scrut >>= \case -- Need to pull out the seed immediately
-- case-label
    Label l params -> case branches BSM.!? qName2Key l <|> d of
      Just body | null params -> fuse (lvl , env , body)
      Just body -> fuse (lvl , env , App body (Forced lvl <$> params)) -- params are already β-d at lvl
      Nothing -> error $ "panic: no label: " <> show l <> " : " <> show params <> "\n; " <> show (BSM.keys branches)
-- case-case: push/copy outer case into each branch, then the inner case fuses with outer case output labels
-- Everything is forced already except branches and d
    CaseB innerScrut ty2 innerBranches innerDefault -> let
      pushCase innerBody = CaseB (Forced lvl innerBody) retT branches d
      optBranches = pushCase <$> innerBranches
      optD        = pushCase <$> innerDefault
      in fuse (lvl , env , CaseB (Forced lvl innerScrut) ty2 optBranches optD)
    opaqueScrut -> pure $ CaseBF (Left opaqueScrut) retT (Right . (lvl,env,) <$> branches) (Right . (lvl,env,) <$> d)

  -- TODO try before and after forcing the scrut
  TTLens scrut [f] LensGet -> simpleTerm' lvl env scrut >>= \case
    LetBlock l -> case V.find ((==f) . iName . fst) l of
--    Just x -> pure $ Right . (lvl,env,) <$> (\(Core t _ty) -> project t) (naiveExpr (snd x))
      Just x -> pure $ Left <$> (\(Core t _ty) -> project t) (naiveExpr (snd x))
    opaque -> pure $ TTLensF (Left opaque) [f] LensGet

  LetBlock lets -> inferBlock lets $ \_ -> LetBlockF <$> lets `forM` \(lm , bind) -> (lm ,) <$> simpleBind lvl env bind
  LetBinds lets inE -> inferBlock lets $ \v -> do
    newLets <- lets `forM` \(lm , bind) -> (lm ,) <$> simpleBind lvl env bind
    newInE  <- simpleTerm' lvl env inE
    pure $ if lvl == 0 then Left <$> project newInE else LetBindsF newLets (Left newInE)

  Forced prevLvl t -> if
    | prevLvl == lvl || prevLvl == 0 -> pure $ Left <$> project t
--  | prevLvl < lvl -> trace (show prevLvl <> " < " <> show lvl :: Text)
--      (fuse (lvl , (did_ $ mkBruijnArgSubs lvl prevLvl , mempty , 0) , t))
  x -> pure $ Right . (lvl , env ,) <$> project x

inferBlock lets go = do
  nest <- letNest <<%= (1+)
  v <- use letBinds >>= \lvl -> V.thaw (snd <$> lets) >>= \v -> MV.write lvl nest v $> v
  go v <* (letNest %= \x -> x - 1) -- <* traceM "decBlock" 

-- TODO how to avoid duplicate simplifications?
-- ie. iff no VBruijns to solve: isEnvEmpty
simpleBind lvl env b = case b of
  BindOK (OptBind optLvl specs) (Core t ty) -> if isEnvEmpty env && optLvl /= 0 then pure b else do
    newT <- simpleTerm' lvl env t
    pure (BindOK (OptBind ({-optLvl +-} 1) specs) (Core newT ty))
  x -> error $ show x

simpleTerm' :: Int -> Env -> Term -> SimplifierEnv s Term
simpleTerm' lvl env t = hypoM (pure . primF) fuse (lvl , env , t)
simpleTerm t = do
  letBinds' <- MV.new 64 -- max let-depth
  simpleTerm' 0 (mempty , mempty) t `evalStateT` FEnv letBinds' 0

simpleExpr :: Expr -> ST s Expr
simpleExpr (Core t ty) = simpleTerm t <&> \t -> Core t ty
simpleExpr _ = pure PoisonExpr

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
