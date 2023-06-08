{-# Language TemplateHaskell #-}
module BetaEnv where
import CoreSyn hiding (JudgedModule(..))
import Externs-- (iNameToBindName , LoadedMod)
import Data.Functor.Foldable as RS
import PrettyCore
import BitSetMap as BSM
import SimplifyInstr
import Control.Lens
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.Map as M
import Data.List (unzip3)

-- A nested Abs inside a β-env smaller than total env requires "inserting" more args
-- this more or less forces us to copy the env, which ruins β-optimal sharing of subcomputations

debug_fuse = True

data FEnv s = FEnv
 { _thisMod    :: ModuleIName
 , _topINames  :: BitSet
 , _loadedMods :: V.Vector LoadedMod
 , _localBinds :: MV.MVector s Bind
 }; makeLenses ''FEnv
type SimplifierEnv s = StateT (FEnv s) (ST s)

getBruijnAbs = \case
  BruijnAbs n body -> Just (n , body)
  BruijnAbsTyped n body _ _ -> Just (n , body)
  _ -> Nothing

type Lvl = Int
data Sub = TSub (V.Vector Sub) Lvl Term deriving Show -- eLen lvl term
type Env = (V.Vector Sub , [Sub]) -- [(Int , Term)]) -- length of argEnv (needs to remain consistent across paps
--type Seed = (Lvl , Env , Term) -- expected eLen may be < envlen since tsubs eLen can increase

data Seed = Seed
  { _lvl  :: Lvl
  , _env  :: Env -- env & trailingArgs
  , _term :: Term
  } deriving Show ; makeLenses ''Seed
isEnvEmpty env = V.null (fst env)

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
fuse seed {-(lvl , env@(argEnv , trailingArgs) , term)-} = use thisMod >>= \modIName -> let
  sLvl = seed ^. lvl
  (argEnv , trailingArgs) = seed ^. env
  continue       tt = Right (seed & term .~ tt)
  continueNoArgs tt = Right (seed & term .~ tt & env . _2 .~ mempty)
  eLen = V.length argEnv
  unSub (TSub prevArgEnv prevLvl arg) | prevLvl == sLvl
    = Right (seed & term .~ arg & env .~ (prevArgEnv , mempty))
 -- unSub (TSub prevArgEnv prevLvl arg) = traceShow (prevLvl , lvl) $ Right (lvl , (prevArgEnv , mempty) , arg)
  noop x = pure $ if null trailingArgs
    then continue <$> project x
    else AppF (continueNoArgs x) (unSub <$> trailingArgs)
  in case seed ^. term of
  App f args -> fuse (seed & env .~ (argEnv , (TSub argEnv sLvl <$> args) <> trailingArgs) & term .~ f)
  abs | Just (n , body) <- getBruijnAbs abs -> if null trailingArgs
    then case getBruijnAbs body of -- not β-reducing => spawn bruijn arg subs
      Just (m , b2) -> fuse (seed & term .~ BruijnAbs (m + n) b2)
      _ -> let
        nextLvl = sLvl + n
        nextSeed = seed & lvl .~ nextLvl & env .~ (mkBruijnArgSubs nextLvl n <> argEnv , mempty) & term .~ body
        in pure $ BruijnAbsF n (Right nextSeed)
    else claimArgs n body trailingArgs where
      claimArgs :: Int -> Term -> [Sub] -> SimplifierEnv s (TermF (Either Term Seed))
      claimArgs n body trailingArgs = let
        (ourArgs , remArgs) = splitAt n trailingArgs
        l = length ourArgs
        in case compare l n of
          EQ -> let nextEnv = V.reverse (V.fromList ourArgs) -- <&> patchAbs l
            in fuse (seed & env .~ (nextEnv <> argEnv , remArgs) & term .~ body)
          LT -> claimArgs l (BruijnAbs (n - l) body) trailingArgs
          GT -> error "impossible"

  VBruijnLevel l -> pure $ let v = sLvl - l - 1
    in if null trailingArgs then VBruijnF v else AppF (Left (VBruijn v)) (unSub <$> trailingArgs)

  -- env contains raw args to simplify, at the new lvl for any bruijns subbed in
  -- This duplicates work if simplifying the same arg twice at the same lvl - need β-optimality
  VBruijn i -> if i >= eLen then error $ show (i , eLen , seed ^. env) else
    argEnv V.! i & \(TSub prevEnv prevLvl argTerm) -> fuse $ seed -- if lvl /= prevLvl then error $ show (lvl , prevLvl)
      & term .~ argTerm
      & env  .~ (prevEnv , trailingArgs)

  -- inlineLetBind: lvl == 0 means this fully reduces (won't produce a function)
  Var (VQBind q) | sLvl == 0 {-&& not (null trailingArgs)-} -> let -- Have to inline all bindings on full β-reduce
    doSimpleBind = \case -- bind = simpleBind lvl (argEnv , []) bind >>= \b -> case b of
      BindOK _ (nL , letCapture) (Core inlineF _ty) ->
--      if && null trailingArgs then pure (Left <$> VarF (VQBind q)) -- may need to inline constants
        fuse $ seed
        & term .~ inlineF
        & env  .~ (V.drop (V.length argEnv - nL) argEnv , trailingArgs)
        -- MV.write bindVec bindName b *> -- if first time seeing the bind
      x -> error (show x)
    in if modName q == modIName
    then use topINames >>= \top -> let bindName = iNameToBindName top (unQName q)
      in use localBinds >>= \bindVec -> MV.read bindVec bindName
--      >>= simpleBind bindName sLvl (seed ^. env . _1 , []) >>= doSimpleBind
        >>= simpleBind q bindName >>= doSimpleBind
    else use loadedMods >>= \lm -> case lookupBindName lm (modName q) (unQName q) of
      Just b  -> doSimpleBind b
      Nothing -> noop (Var (VQBind q))

  Var (VQBind q) | modName q == modIName -> do
    -- TODO runSimpleTerm here may duplicates work (the simpleExprF in the cata)
    -- should make custom hypo with a Left and a Skip embedded in TermF
    args <- trailingArgs `forM` \(TSub e l t) -> if null e then pure t else runSimpleTerm (Seed l (e , []) t)
    specApp sLvl (argEnv , []) q args

  LetSpec q sh | sLvl == 0 && modName q == modIName -> use localBinds >>= \bindVec -> use topINames >>= \top ->
    let bindName = iNameToBindName top (unQName q) in
    MV.read bindVec bindName
    >>= simpleBind q bindName >>= \case
      BindOK (OptBind _ shps) _ _ -> case shps M.!? sh of
        Nothing -> error $ show (modName q , unQName q) <> ": " <> show shps -- pure (LetSpecF q sh) -- ?! error
        Just t  -> if null trailingArgs then pure (SkipF (Left t)) else fuse (seed & term .~ t)
      x -> error $ show x

  Label l ars -> pure $ LabelF l ((continueNoArgs <$> ars) <> (unSub <$> trailingArgs))

  -- ? where do params come from if no trailing args here
  -- TODO what if stacking case-cases
  -- TODO maybe don't need to force the scrut?
  CaseSeq n scrut retT branches d -> if not (null trailingArgs) then _ else
--  runSimpleTerm (Seed sLvl (argEnv , []) scrut) >>= \scrut -> -- scrut is already simplified
    fuseCase (seed & term .~ scrut & env . _1 %~ V.drop n) retT branches d

  --Have to simplify scrut first, it doesn't take our trailingArgs!
  CaseB scrut retT branches d -> runSimpleTerm (Seed sLvl (argEnv , []) scrut) >>= \scrut ->
    fuseCase (seed & term .~ scrut) retT branches d

  -- Try before and after forcing the scrut
  TTLens obj [f] LensGet -> case obj of
    l@Label{} -> error $ "Lensing on a label: " <> show (l , f)
    Tuple l -> pure $ continue <$> project (l V.! unQName (QName f))
    Prod  l -> pure $ continue <$> project (fromMaybe (error "panic: absent field") $ l BSM.!? f)
    scrut | null trailingArgs -> runSimpleTerm (seed & term .~ scrut) >>= \case
      Tuple l -> pure $ SkipF $ Left $ (l V.! unQName (QName f))
      Prod  l -> pure $ SkipF $ Left $ (fromMaybe (error "panic: absent field") $ l BSM.!? f)
      opaque -> pure $ TTLensF (Left opaque) [f] LensGet

  RenameCaptures free inExpr -> error ("Rename captures: " <> show free <> " in\n" <> show inExpr)
  x -> noop x

--fuseCase lvl argEnv trailingArgs retT branches d tt = let
fuseCase seed retT branches d = let
  idEnv = mkBruijnArgSubs (seed ^. lvl) (V.length (seed ^. env . _1))
  continue tt = Right (seed & term .~ tt)
  in case seed ^. term of
  -- case-label: params are already β-d at this lvl, so idSubs (not ideal solution though)
  Label l params -> case branches BSM.!? qName2Key l <|> d of
    Just body -> fuse $ seed & term .~ body
      & env . _2 %~ \trailingArgs -> (params <&> TSub idEnv (seed ^. lvl)) <> trailingArgs
    Nothing -> error $ "panic: no label: " <> show l <> " : " <> show params <> "\n; " <> show (BSM.keys branches)
  -- case-case: push(copy) outer case to each branch, then the inner case output fuses with outer case labels
  CaseB innerScrut ty2 innerBranches innerDefault -> let
    pushCase = \case -- this will produce a case-label for each branch
      -- case (\p1..p2 -> scrut) of branches
      -- (\p1..p2 C -> ) (p1..p2 -> scrut) (\case branches) -- Thus branches aren't touched by params
      -- CaseSeq knows its branches expect it to rm the first n args of its env
      BruijnAbs n innerOutput -> BruijnAbs n (CaseSeq n innerOutput retT branches d)
      BruijnAbsTyped{} -> _
      innerOutput      -> CaseB innerOutput retT branches d
    in fuseCase (seed & term .~ innerScrut) ty2 (pushCase <$> innerBranches) (pushCase <$> innerDefault)
  -- no-fusion
  CaseSeq{} -> error "" -- CaseSeq should be dealt with almost immediately after spawning
  opaqueScrut -> pure $ CaseBF (Left opaqueScrut) retT (continue <$> branches) (continue <$> d)

simpleBindings :: ModuleIName -> BitSet -> V.Vector LoadedMod -> V.Vector (LetMeta , Bind)
  -> ST s (V.Vector (LetMeta , Bind))
simpleBindings modIName topINames loadedMods lets = let
  go = lets `iforM` \bindName (lm , bind) -> (lm ,) <$> simpleBind (letName lm) bindName bind
  in V.thaw (snd <$> lets) >>= \locals -> go `evalStateT` FEnv modIName topINames loadedMods locals

-- simplifies a binding by itself in a void env (captures must be explicitly applied to bindings)
simpleBind q bindName bind = use localBinds >>= \bindVec -> case bind of
  BindOK (OptBind optLvl specs) free (Core t ty) -> if optLvl /= 0 then pure bind else do
    MV.write bindVec bindName (BindOK (OptBind 1 specs) free (Core (Var (VQBind q)) ty))
    newT <- runSimpleTerm (Seed 0 (mempty , mempty) t)
    let b = BindOK (OptBind ({-optLvl +-} 1) specs) free (Core newT ty)
    b <$ MV.write bindVec bindName b
  x -> error (show x)

runSimpleTerm :: Seed -> SimplifierEnv s Term
runSimpleTerm seed = let
-- hypoM but with Skip node
  termFHypoM :: (Monad m , Recursive b , Base b ~ TermF)
    => (TermF b -> b) -> (c -> m (TermF (Either b c))) -> c -> m b
  termFHypoM f g = let
    go = (\case { SkipF s -> (pure . cata f ||| h) s ; x -> fmap f (traverse (pure . cata f ||| h) x) })
    h  = go <=< g
    in h
  in {-hypoM-} termFHypoM constFoldF fuse seed

--simpleExpr :: Expr -> ST s Expr
--simpleExpr (Core t ty) = simpleTerm t <&> (`Core` ty)

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
--  Var (VLetBind q) -> pure ([] , [arg] , ShapeLetBind q)
    -- avoid specialising on builtins, which can never fuse
--  App (Var (VLetBind q)) ars -> traverse solveArg ars <&> \ars ->
--    unzip3 ars & \(uL , rL , shL) -> (concat uL , [App (Var (VLetBind q)) (concat rL)] , ShapePAPLet q shL)
    Label l ars -> traverse solveArg ars <&> \case
      [] -> ([] , [Label l []] , ShapeLabel l []) -- lone label is like a constant VQBind
      ars -> unzip3 ars & \(uL , rL , shL) -> (concat uL , [Label l (concat rL)] , ShapeLabel l shL)
    rawArg         -> gets identity >>= \bruijn -> modify (1+) $> ([rawArg] , [VBruijn bruijn] , ShapeNone)
  in (bruijnN , reverse $ concat unstructuredArgsL , concat repackedArgsL , argShapes)
  -- Need to reverse unstructuredArgs since our deBruijns are assigned in reverse order

-- TODO atm only specialises current module
specApp :: forall s. Lvl -> Env -> QName -> [Term] -> SimplifierEnv s (TermF (Either Term Seed))
specApp seedLvl env q args = let
  noInline = SkipF (Left (App (Var (VQBind q)) args))
  (bruijnN , unstructuredArgs , repackedArgs , argShapes) = destructureArgs args
  in -- d_ args $ d_ argShapes $ d_ repackedArgs $ d_ unstructuredArgs $ d_ "" $
  if all (== ShapeNone) argShapes {- note. all _ [] = True -} then pure noInline else
  use localBinds >>= \bindVec -> use topINames >>= \top -> let bindNm = iNameToBindName top (unQName q)
  in MV.read bindVec (bindNm) >>= \case
  BindOK o _free expr@(Core inlineF _ty) -> case bindSpecs o M.!? argShapes of
    Just cachedSpec -> pure $ SkipF $ Left (App cachedSpec unstructuredArgs)
    Nothing -> if all (\case { ShapeNone -> True ; _ -> False }) argShapes then pure noInline else do
      let recGuard = LetSpec q argShapes
      MV.modify bindVec (\(BindOK (OptBind oLvl oSpecs) free _t)
        -> BindOK (OptBind oLvl (M.insert argShapes recGuard oSpecs)) free expr) bindNm

      -- ! repackedArgs are at lvl, inlineF is at (lvl + bruijnN)
      -- fully simplify the specialised partial application (if it recurses then this spec is extremely valuable)
      let rawAbs = BruijnAbs bruijnN (App inlineF repackedArgs)
      specFn <- runSimpleTerm (Seed seedLvl env rawAbs) -- TODO if repackedArgs contains debruijns this may break
      -- (fst env , TSub (mkBruijnArgSubs lvl (V.length (fst env))) (bruijnN + lvl) <$> repackedArgs) rawAbs
      when debug_fuse $ do
        traceM $ "raw spec " <> show bindNm <> " " <> show argShapes <> "\n => " <> prettyTermRaw rawAbs <> "\n"
        traceM $ "simple spec " <> prettyTermRaw specFn <> "\n"

      MV.modify bindVec (\(BindOK (OptBind oLvl oSpecs) free _t)
        -> BindOK (OptBind oLvl (M.insert argShapes specFn oSpecs)) free expr) bindNm

      let fn = if seedLvl == 0 then specFn else recGuard
      pure $ SkipF $ Left $ if null unstructuredArgs then fn else App fn unstructuredArgs
  _ -> pure noInline
