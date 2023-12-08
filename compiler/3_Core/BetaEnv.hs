{-# Language TemplateHaskell #-}
module BetaEnv where
import CoreSyn hiding (JudgedModule(..))
import Externs
import Prim(Literal(..))
import Data.Functor.Foldable as RS
import PrettyCore
import BitSetMap as BSM
import SimplifyInstr
import Control.Lens
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.Map as M
import qualified Data.IntMap as IM
import Data.List (unzip3)

g_runSimplify = False

g_reduceInstr = g_runSimplify
g_noInline = not g_runSimplify

-- A nested Abs inside a β-env smaller than total env requires "inserting" more args
-- this more or less forces us to copy the env, which ruins β-optimal sharing of subcomputations

debug_fuse = False

data FEnv s = FEnv
 { _thisMod    :: ModuleIName
 , _loadedMods :: V.Vector LoadedMod
 , _localBinds :: MV.MVector s Bind
 }; makeLenses ''FEnv
type SimplifierEnv s = StateT (FEnv s) (ST s)

getBruijnAbs = \case
  BruijnAbs n _ body -> Just (n , body)
  BruijnAbsTyped n body _ _ -> Just (n , body)
  _ -> Nothing

type Lvl = Int
data Sub = TSub (V.Vector Sub) Lvl Term deriving Show -- eLen lvl term
type Env = (V.Vector Sub , [Sub]) -- length of argEnv (needs to remain consistent across paps
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
fuse seed = use thisMod >>= \modIName -> let -- trace (prettyTermRaw (seed ^. term)) $ let
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
      Just (m , b2) -> fuse (seed & term .~ BruijnAbs (m + n) mempty b2)
      _ -> let
        nextLvl = sLvl + n
        nextSeed = seed & lvl .~ nextLvl & env .~ (mkBruijnArgSubs nextLvl n <> argEnv , mempty) & term .~ body
        in pure $ BruijnAbsF n mempty (Right nextSeed)
    else claimArgs n body trailingArgs where
      claimArgs :: Int -> Term -> [Sub] -> SimplifierEnv s (TermF (Either Term Seed))
      claimArgs n body trailingArgs = let
        (ourArgs , remArgs) = splitAt n trailingArgs
        l = length ourArgs
        in case compare l n of
          EQ -> let nextEnv = V.reverse (V.fromList ourArgs) -- <&> patchAbs l
            in fuse (seed & env .~ (nextEnv <> argEnv , remArgs) & term .~ body)
          LT -> claimArgs l (BruijnAbs (n - l) mempty body) trailingArgs
          GT -> error "impossible"

  VBruijnLevel l -> pure $ let v = sLvl - l - 1
    in if null trailingArgs then VBruijnF v else AppF (Left (VBruijn v)) (unSub <$> trailingArgs)

  -- env contains raw args to simplify, at the new lvl for any bruijns subbed in
  -- This duplicates work if simplifying the same arg twice at the same lvl - need β-optimality
  VBruijn i -> if i >= eLen then error $ show (i , eLen , seed ^. env) else
    argEnv V.! i & \(TSub prevEnv prevLvl argTerm) -> fuse $ seed
    -- if lvl /= prevLvl then error $ show (lvl , prevLvl)
      & term .~ argTerm
      & env  .~ (prevEnv , trailingArgs)

  -- inlineLetBind: lvl == 0 means this fully reduces (won't produce a function)
  Var (VQBindIndex q) | g_reduceInstr && sLvl == 0 && not g_noInline {-&& not (null trailingArgs)-} -> let -- Have to inline all bindings on full β-reduce
    doSimpleBind = \case -- bind = simpleBind lvl (argEnv , []) bind >>= \b -> case b of
--    BindOK o (Core (Var (VQBindIndex qq)) _ty) | q == qq -> d_ "error bind contains itself" $ noop (Var (VQBindIndex q))
      BindOK _o (Core inlineF _ty) -> -- d_ inlineF $ -- if optId o /= 0 then noop inlineF else
--      if null trailingArgs then noop (Var (VQBind q)) else
--      if && null trailingArgs then pure (Left <$> VarF (VQBind q)) -- may need to inline constants
        fuse $ seed
        & term .~ inlineF
        & env  .~ ({-V.drop (V.length argEnv - nL)-} {-argEnv-} mempty , trailingArgs)
      x -> error (show x)
    in if modName q == modIName
    then runSimpleBind q >>= doSimpleBind
    else use loadedMods >>= \lm -> case lookupBind lm (modName q) (unQName q) of
      Just b  -> doSimpleBind b
      Nothing -> noop (Var (VQBindIndex q))

  Var (VQBindIndex q) | modName q == modIName && not g_noInline ->
--  runSimpleBind q *>
    (trailingArgs `forM` \(TSub e l t) -> if null e then pure t else runSimpleTerm (Seed l (e , []) t))
    >>= specApp sLvl (argEnv , []) q

  LetSpec q sh | sLvl == 0 && modName q == modIName -> runSimpleBind q >>= \case
    BindOK (OptBind _ shps) _ -> case shps M.!? sh of
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
  CaseB scrut retT branches d -> runSimpleTerm (Seed sLvl (argEnv , []) scrut)
    >>= \scrut -> fuseCase (seed & term .~ scrut) retT branches d

  -- Try before and after forcing the scrut
  TTLens obj [f] LensGet -> case obj of
    l@Label{} -> error $ "Lensing on a label: " <> show (l , f)
    Tuple l -> pure $ continue <$> project (l V.! unQName (QName f))
    Prod  l -> pure $ continue <$> project (fromMaybe (error "panic: absent field") $ l BSM.!? f)
    scrut | null trailingArgs -> runSimpleTerm (seed & term .~ scrut) >>= \case
      Tuple l -> pure $ SkipF $ Left $ (l V.! unQName (QName f))
      Prod  l -> pure $ SkipF $ Left $ (fromMaybe (error "panic: absent field") $ l BSM.!? f)
      opaque -> pure $ TTLensF (Left opaque) [f] LensGet
    opaque -> pure $ TTLensF (continue opaque) [f] LensGet

  Captures (VQBindIndex q) | modName q == modIName -> let bindName = unQName q
    in use localBinds >>= \bindVec -> MV.read bindVec bindName >>= \case
    BindOK{} -> fuse $ seed & term .~ Var (VQBindIndex q) -- recursive def doesn't capture anything
    BindRenameCaptures atLen letCaptures _ -> let
      -- v capture in recursive position: need to find the args and adjust them to this lvl
      -- perhaps ideally should let the top-level renameCaptures rename them for us..
      new = popCount letCaptures
      captures = bitSet2IntList letCaptures <&> \i -> VBruijnLevel $
        atLen - new - renameVBruijn atLen letCaptures i
      in fuse $ seed & term .~ App (Var (VQBindIndex q)) (reverse captures)
    x -> error (show x)
  x -> noop x

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
      BruijnAbs n dups innerOutput -> BruijnAbs n dups (CaseSeq n innerOutput retT branches d)
      BruijnAbsTyped{} -> _
      innerOutput      -> CaseB innerOutput retT branches d
    in fuseCase (seed & term .~ innerScrut) ty2 (pushCase <$> innerBranches) (pushCase <$> innerDefault)
  -- no-fusion
  CaseSeq{} -> error "" -- CaseSeq should be dealt with almost immediately after spawning
  opaqueScrut -> pure $ CaseBF (Left opaqueScrut) retT (continue <$> branches) (continue <$> d)

simpleBindings :: ModuleIName -> V.Vector LoadedMod -> V.Vector (LetMeta , Bind)
  -> ST s (V.Vector (LetMeta , Bind))
simpleBindings modIName loadedMods lets = let
  go = lets `iforM` \bindName (lm , bind) -> (lm ,) <$> simpleBind bindName bind
  in V.thaw (snd <$> lets) >>= \locals -> go `evalStateT` FEnv modIName loadedMods locals

runSimpleBind q = let bindName = unQName q -- only works in this module!
  in use localBinds >>= \bindVec -> MV.read bindVec bindName >>= simpleBind bindName

-- simplifies a binding by itself in a void env (captures must be explicitly applied to bindings)
simpleBind bindName bind = use localBinds >>= \bindVec -> case bind of
  BindOK (OptBind optLvl specs) (Core t ty) -> if optLvl /= 0 then pure bind else do
--  MV.write bindVec bindName (BindOK (OptBind 1 specs) (Core (Var (VQBind q)) ty))
    newT <- runSimpleTerm (Seed 0 (mempty , mempty) t)
    let b = BindOK (OptBind ({-optLvl +-} 1) specs) (Core newT ty)
    b <$ MV.write bindVec bindName b
  BindRenameCaptures atLen free (Core inExpr ty) -> let
    -- v TODO captures don't need renaming if they are in range [0..n] for some n < atLen
    -- namesOK = 1 + freeVars == 1 .<<. atLen
    nCaptures = popCount free
    renameEnv = V.generate atLen
      (\i -> TSub mempty nCaptures (VBruijnLevel (nCaptures - 1 - renameVBruijn atLen free i)))
    seed = Seed nCaptures (renameEnv , mempty) inExpr
    in do
      term <- BruijnAbs nCaptures mempty <$> runSimpleTerm seed
      let b = BindOK (OptBind 1 mempty) (Core term ty) -- Any recursive captures were sorted
     --   b = BindRenameCaptures atLen free (Core term ty)
      b <$ MV.write bindVec bindName b
  x -> error (show x)

-- Renaming vbruijns within functions that capture part of the environment:
--vv free = 26 , bitset2IntList 26 = [1,3,4] means (1 => 0 , 3 => 1 , 4 => 2)
--eg. on free=26: renamedVBruijn[0..atlen-1] = [(0,-1),(1,0),(2,0),(3,1),(4,2),(5,2)],
--  -- (atLen is the ref lvl where captures are valid bruijnidxs)
renameVBruijn :: Int -> BitSet -> Int -> Int
renameVBruijn atLen free i = if
  | i >= atLen     -> error "impossible"
  | testBit free i -> popCount (setNBits (i + 1) .&. free) - 1 -- & \r -> d_ (i , r , free) r
  | True -> i

runSimpleTerm :: Seed -> SimplifierEnv s Term
runSimpleTerm seed = let
-- hypoM but with Skip node
  termFHypoM :: (Monad m)
    => (TermF b -> b) -> (c -> m (TermF (Either Term c))) -> c -> m b
  termFHypoM f g = let
    h = g >=> \case
      SkipF s -> (pure . cata f ||| h) s
      x       -> f <$> traverse (pure . cata f ||| h) x
    in h
--in termFHypoM constFoldCountF fuse seed <&> \(dups , rhs) -> rhs
  in termFHypoM constFoldF fuse seed

constFoldF :: TermF Term -> Term
constFoldF = \case
  AppF (Instr i) args | g_reduceInstr -> simpleInstr i args
  AppF (App g args) brgs -> constFoldF (AppF g (args <> brgs))
  InstrAppF{} -> _
  CastF (CastZext n) (Lit (Fin m i)) | m < n -> Lit (Fin n i)
  x -> embed x

type Dups = IM.IntMap Int
_constFoldCountF :: TermF (Dups , Term) -> (Dups , Term)
_constFoldCountF termDups = let
  term = snd <$> termDups
  dups = foldr (\x acc -> IM.unionWith (+) acc (fst x)) mempty termDups
  in case term of
  VBruijnF i -> (IM.singleton i 1 , VBruijn i)
  -- TODO only take args this scopes over
  BruijnAbsF n _ rhs -> d_ dups (mempty , BruijnAbs n dups rhs)
--CaseBF{} ->
  BruijnAbsTypedF n rhs args rT -> error $ show (embed term)
  term' -> (dups,) $ case term' of
    AppF (Instr i) args -> simpleInstr i args
--  AppF (App g args) brgs -> constFoldCountF (AppF g (args <> brgs))
    CastF (CastZext n) (Lit (Fin m i)) | m < n -> Lit (Fin n i)
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
    Var (VQBindIndex q)   -> pure ([] , [arg] , ShapeQBind q)
    Label l ars -> traverse solveArg ars <&> \case
      [] -> ([] , [Label l []] , ShapeLabel l []) -- lone label is like a constant VQBind
      ars -> unzip3 ars & \(uL , rL , shL) -> (concat uL , [Label l (concat rL)] , ShapeLabel l shL)
    rawArg         -> gets identity >>= \bruijn -> modify (1+) $> ([rawArg] , [VBruijn bruijn] , ShapeNone)
  in (bruijnN , reverse $ concat unstructuredArgsL , concat repackedArgsL , argShapes)
  -- Need to reverse unstructuredArgs since our deBruijns are assigned in reverse order

-- TODO atm only specialises current module
specApp :: forall s. Lvl -> Env -> QName -> [Term] -> SimplifierEnv s (TermF (Either Term Seed))
specApp seedLvl env q args = let
  noInline = let fn = Var (VQBindIndex q)
    in if null args then SkipF (Left fn) else SkipF (Left (App (fn) args))
  (bruijnN , unstructuredArgs , repackedArgs , argShapes) = destructureArgs args
  in -- d_ args $ d_ argShapes $ d_ repackedArgs $ d_ unstructuredArgs $ d_ "" $
  if all (== ShapeNone) argShapes {- note. all _ [] = True -} then pure noInline else
  use localBinds >>= \bindVec ->
    let bindNm = unQName q
  in MV.read bindVec bindNm >>= \case
  BindOK o expr@(Core inlineF _ty) -> case bindSpecs o M.!? argShapes of
    Just cachedSpec -> pure $ SkipF $ Left (App cachedSpec unstructuredArgs)
    Nothing -> if all (\case { ShapeNone -> True ; _ -> False }) argShapes then pure noInline else do
      let recGuard = LetSpec q argShapes
      MV.modify bindVec (\(BindOK (OptBind oLvl oSpecs) _t)
        -> BindOK (OptBind oLvl (M.insert argShapes recGuard oSpecs)) expr) bindNm

      -- ! repackedArgs are at lvl, inlineF is at (lvl + bruijnN)
      -- fully simplify the specialised partial application (if it recurses then this spec is extremely valuable)
      let rawAbs = BruijnAbs bruijnN mempty (App inlineF repackedArgs)
      specFn <- runSimpleTerm (Seed seedLvl env rawAbs) -- TODO if repackedArgs contains debruijns this may break
      -- (fst env , TSub (mkBruijnArgSubs lvl (V.length (fst env))) (bruijnN + lvl) <$> repackedArgs) rawAbs
      when debug_fuse $ do
        traceM $ "raw spec " <> show bindNm <> " " <> show argShapes <> "\n => " <> prettyTermRaw rawAbs <> "\n"
        traceM $ "simple spec " <> prettyTermRaw specFn <> "\n"

      MV.modify bindVec (\(BindOK (OptBind oLvl oSpecs) _t)
        -> BindOK (OptBind oLvl (M.insert argShapes specFn oSpecs)) expr) bindNm

      let fn = if seedLvl == 0 then specFn else recGuard
      pure $ SkipF $ Left $ if null unstructuredArgs then fn else App fn unstructuredArgs
  _ -> pure noInline
