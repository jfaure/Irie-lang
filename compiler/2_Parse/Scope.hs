{-# Language TemplateHaskell #-}
module Scope (scopeTT , scopeApoF , initModParams , Params , findDups) where
import ParseSyntax
import QName
import CoreSyn(ExternVar(..))
import Mixfix (solveMixfixes)
import Externs ( checkExternScope , Externs )
import Errors
import Data.Functor.Foldable
import Control.Lens
import Data.List (span)
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV

-- * IConv: each module has its own isomorpism convention (HName <-> IName)
-- * QName is thus a module name (indicating the IConv) and an IName
-- ? QTT requires cata to track mulitplicity (0 | 1 | ω)
data Params = Params
  { _open        :: BitSet
  , _lets        :: BitSet
  , _args        :: BitSet
  , _bruijnMap   :: V.Vector Int -- pre-built by mkCase: text IName -> BruijnArg TODO merge with letMap
  , _bruijnCount :: Int -- nesting level
  , _letMap      :: V.Vector (IName , Int , Int , Int) -- iname , letNest let idx , lifted index in module binds
                                             -- unfortunately must keep the letName in case its a (mutual?) forward ref
  , _letNest     :: Int
  , _openDatas   :: (BitSet , V.Vector Int) -- let-offset , else IName == labelName
  } deriving Show ; makeLenses ''Params

initModParams letCount modOpens open bindNmsV = let -- d_ modOpens $ let
  sz = 2048 -- TODO max number of let-nests and / or bruijn args
  openDatas = let
    getOpens = \case
      POpenData lOff inms -> inms <&> \i -> (lOff , i)
      _ -> []
    in concatMap getOpens modOpens
  openDatasBitSet = intList2BitSet (snd <$> openDatas)
  openDatasV = V.create $ MV.new sz >>= \v -> v <$ (openDatas `forM_` \(lOff , i) -> MV.write v i lOff)
  letMap = V.create $ MV.new sz >>= \v -> v <$ do
    bindNmsV `iforM_` \l i -> MV.write v i (i , 0 , l , l) -- top-binds written to modBinds without offset
  initParams = Params open emptyBitSet emptyBitSet (V.create (MV.new sz)) 0 letMap 0 (openDatasBitSet , openDatasV)
  in initParams & \params -> params
  & lets %~ (.|. intList2BitSet bindNmsV)
  & letNest %~ (1+)

findDups :: Foldable t => t Int -> BitSet
findDups iNames = let
  fn i (dups , mask) = (if testBit mask i then setBit dups i else dups , setBit mask i)
  in fst $ foldr fn ((0 , 0) :: (BitSet , BitSet)) iNames

-- TODO don't allow `bind = lonemixfixword`
-- handleExtern (readParseExtern open mod e i) ||| readQParseExtern :: ExternVar
handleExtern :: Externs -> Int -> BitSet -> V.Vector (IName , Int , Int , Int) -> Int -> TT
handleExtern exts mod open lm i = case checkExternScope open mod exts i of
  ForwardRef b  -> Var (VLetBind (lm V.! b))
  Imported _ e  -> InlineExpr e
  MixfixyVar m  -> MFExpr (-1) m -- TODO if ko, mixfix should report "mixfix word cannot be a binding: "
  -- (errors . scopeFails %= s)
  NotOpened m h -> ScopePoison (ScopeNotImported m h)
  NotInScope  h -> ScopePoison (ScopeError h)
  AmbiguousBinding h ms -> ScopePoison (AmbigBind h ms)
  ImportLabel q   -> QLabel q
  Importable m i  -> QVar (mkQName m i)

-- Pattern (TT) inversion: case-alts can introduce VBruijns and thus change the scope environment
-- Parse > resolve mixfixes > resolve cases > check arg scopes?
-- note: codo on cofree comonad => DSL for case analysis on the base functor of the cofree comonad.

-- β-optimality for sharing branches between different paps in dependency tree
-- [ [Pattern , TT] ] -> [ Case ]        2 ^ (nArgs - 1) paps

-- * name scope , free variables , dup nodes , resolve VExterns to BruijnArg | QName
-- unpattern assigns debruijn levels: bl, the debruijn index is lvl - bl - 1
type Seed = (TT , Params)
scopeApoF :: Int -> Externs -> ModuleIName -> Seed -> TTF (Either TT Seed)
scopeApoF topBindsCount exts thisMod (this , params) = let
  scopeBruijnAbs :: BruijnAbsF TT -> TTF (Either TT Seed)
  scopeBruijnAbs (BruijnAbsF n bruijnSubs _ tt) = let
    argsSet    = intList2BitSet (fst <$> bruijnSubs)
    warnShadows ret = let argShadows = params._args .&. argsSet ; letShadows = params._lets .&. argsSet in if
      | argShadows /= 0 -> ScopeWarn (LambdaShadows argShadows) ret
      | letShadows /= 0 -> ScopeWarn (LetShadows letShadows) ret
      | otherwise -> ret
    absParams = params & args %~ (.|. argsSet)
                       & bruijnCount %~ (+ n)
                       & bruijnMap %~ V.modify (\v -> bruijnSubs `forM_` \(i , b) -> MV.write v i b)
    in BruijnLamF $ BruijnAbsF n [] params._bruijnCount (Right (warnShadows tt , absParams))

  updateLetParams params liftName bindNms = params
    & lets %~ (.|. intList2BitSet bindNms)
    & letNest %~ (1+)
    & letMap %~ V.modify (\v -> bindNms `iforM_` \i e ->
      MV.write v e (e , params._letNest , i , i + topBindsCount + liftName))
  resolveExt :: Int -> TT
  resolveExt i = if
    | params._args `testBit` i -> Var $ VBruijn  (params._bruijnCount - 1 - (params._bruijnMap V.! i))
    | params._lets `testBit` i -> Var $ VLetBind (params._letMap V.! i)
    | fst params._openDatas `testBit` i -> snd params._openDatas V.! i & \e -> LabelDecl i e
    | otherwise -> handleExtern exts thisMod (params ^. Scope.open) params._letMap i

  -- Patterns (- TTs) need their labels and constants scoped, then introduce new args
  -- - A (B a _) C => rhs1
  --   _  => rhs2
  -- + \s0 => guard s0 A \s1 => guard s1 B \s2 s3 => name s2 = a => guard s3 C => rhs
  -- = \s0 => case s0 of { A s1 => case s1 of { B (s2=a) s3 => case s3 of { C => rhs }}}
  -- failures : redundant pattern match / illegal pattern
  -- Case /guard failures are recoverable iff wildcard higher case next: this duplicates rhs
  -- ! This delegates spawning of new VBruijns via GuardArgs
  unfoldCase :: TT -> [(TT , TT)] -> Params -> TT
  unfoldCase scrut rawAlts params = let
    -- * resolve enough externs to run solvemixfix on the pattern
    scopeLayer pat = case pat of
      VParseIName i -> case checkExternScope params._open thisMod exts i of
        ImportLabel q -> QLabel q
--      ForwardRef i  -> LabelDecl i
        _ -> if fst params._openDatas `testBit` i
          -- data declarations contain "let-binds" describing a specific type for this label
          then snd params._openDatas V.! i & \e -> LabelDecl i e
          else VParseIName i -- new argument. (x is likely: `NotInScope sometxt`)
      Juxt o args -> solveMixfixes o (scopeLayer <$> args) -- TODO need to solveScope VExterns first
      tt -> tt
    isLabel = \case { QLabel{} -> True ; Label{} -> True ; App{} -> True; _ -> False }
    (altPats , rest) = span (isLabel . fst) (first scopeLayer <$> rawAlts)
    fail serr = (Right 0 , ScopePoison serr)
    -- Left if a label binding, else a raw label that may take any type
    alts = altPats <&> \(pat {-, guards)-} , rhs) -> case pat of
      QLabel q -> (Right (qName2Key q) , rhs) -- Guards openMatch guards rhs)
      Label i subPats             -> (Right (qName2Key (mkQName thisMod i)) , GuardArgs subPats rhs)
      App _ (QLabel q) subPats    -> (Right (qName2Key q) , GuardArgs subPats rhs)
      App _ (LabelDecl i e) subPats -> (Left ((mkQName thisMod i) , e) , GuardArgs subPats rhs)
      App _ (VParseIName i) ars   -> fail (NoScopeLabel i (length ars))
      x -> fail (ScopeError $ "bad pattern: " <> show x)
    openMatch = case rest of -- TODO could be guarded; another case
      [] -> Nothing
      (WildCard , rhs) : redundant -> Just rhs -- guards
      x -> Just (ScopePoison (ScopeError $ "Unknown label: " <> show x))
--    x -> error (show x) -- _illegallPattern -- argProd , Tuple , Lit are parsed as guards
    match = MatchB scrut alts openMatch
   in match -- (if null redundant then identity else ScopeWarn RedundantPatMatch) (match (Just wild))

  -- Spawn new VBruijns and Guard them if further cases required
  -- a guard is recoverable if an enclosing case has a wildcard
  -- nestGuards: enclosing guards on top of subpatterns for these args
  guardArgs [] rhs [] = RawExprF (Right (rhs , params))
  guardArgs args rhs nestGuards = let -- TODO use the fallback (happens when labels are matched..)
    n = length args
    lvl = params._bruijnCount :: Int
    vbruijnLvls = [lvl .. lvl + n-1] -- [n-1 , n-2 .. 0]
    argSubs = let getArgSub i = \case { VParseIName e -> [(e , i)] ; _ -> [] }
      in concat (zipWith getArgSub vbruijnLvls args)
    mkGuards pat vbl = case pat of
      VParseIName{} -> []
      WildCard{} -> []
      pat -> [GuardPat pat (Var (VBruijnLevel vbl))]
    guards = concat (zipWith mkGuards args vbruijnLvls) :: [Guard]
    in scopeBruijnAbs $ BruijnAbsF n argSubs 0 (Guards Nothing (guards ++ nestGuards) rhs)

  in case {-d_ (embed $ Question <$ this) -} this of
  VParseIName i -> Left <$> project (resolveExt i)
  Var v -> case v of
    VBruijnLevel i -> VarF (VBruijn $ params._bruijnCount - 1 - i) -- Arg-prod arg name
    VBruijn n -> VarF (VBruijn n) -- lambdaCaseF spawns (VBruijn 0) ; error "VBruijn n/=0 shouldn't be possible"
  -- TODO Not ideal; retype solvemixfix on (∀a. TTF a) ?
  Juxt o args   -> Left <$> project (solveMixfixes o $ scopeTT topBindsCount exts thisMod params <$> args)
--Juxt o args   -> scopeApoF exts thisMod . (,params) $ solveMixfixes o $ _ $
--  args <&> \case { Var v -> handleVar v ; x -> Left <$> project x }
  BruijnLam b -> scopeBruijnAbs b
  LambdaCase (CaseSplits' alts) -> scopeBruijnAbs $ BruijnAbsF 1 [] 0 (CasePat (CaseSplits (Var (VBruijn 0)) alts))
  CasePat (CaseSplits scrut alts) -> RawExprF (Right (unfoldCase scrut alts params , params))

  -- v transpose ?
  FnEqns eqns -> case eqns of
    [GuardArgs pats rhs] -> guardArgs pats rhs []
    fns -> DesugarPoisonF (IllegalPattern $ show (length fns) <> " function equations (This might be supported in the future):\n" <> show fns)
  GuardArgs pats rhs -> guardArgs pats rhs []
  Guards _ko [] rhs -> scopeApoF topBindsCount exts thisMod (rhs , params) -- RawExprF (Right (rhs , params)) -- skip
  Guards ko (g : guards) rhs -> let
    guardLabel scrut q subPats = fmap (Right . (,params)) $ let
      rhs' = if null subPats then Guards ko guards rhs else GuardArgs subPats (Guards ko guards rhs)
      in MatchBF scrut [(Right (qName2Key q) , rhs')] ko
    in case g of
    GuardPat pat scrut -> case pat of -- TODO should probably let unfoldCase take over everything
      Label l subPats -> guardLabel scrut (mkQName thisMod l) subPats
      Tuple subPats -> let
        n = length subPats
        projections = [TupleIdx (qName2Key (mkQName 0 i)) scrut | i <- [0 .. n - 1]]
        in Right . (,params) <$> AppF (-1) (GuardArgs subPats (Guards ko guards rhs)) projections
--    -- vv TODO could be Label or new arg
--    Var (VExtern i) -> case checkExternScope params._open thisMod exts i of
--      ImportLabel q -> guardLabel scrut q []--guards
--      NotInScope _  -> scopeBruijnAbs (BruijnAbsF 1 [(i , params._bruijnCount)] 0 rhs)
--      x -> DesugarPoisonF (IllegalPattern ("Ext: " <> show x))
      x -> RawExprF (Right (unfoldCase scrut [(x , rhs)] params , params))
--    x -> DesugarPoisonF (IllegalPattern (show x))
    GuardBool{} -> error (show g)

  -- ? mutual | let | rec scopes
  LetIn (Block open letType binds) liftNames mtt -> let
    letParams = updateLetParams params liftNames (toList (binds <&> _fnIName))
    bindsDone :: V.Vector FnDef
    bindsDone = binds <&> (& fnRhs %~ scopeTT topBindsCount exts thisMod letParams)
    dups = fst $ foldr (\i (dups , mask) -> (if testBit mask i then setBit dups i else dups , setBit mask i))
      ((0 , 0) :: (BitSet , BitSet)) (binds <&> (^. fnIName))
--  vv TODO get the inames
--  dupHNames = bitSet2IntList dups <&> \i -> bindsDone V.! i ^. fnNm
    letTT = LetInF (Block open letType bindsDone) liftNames (Right (mtt , letParams))
    in if dups == 0 then letTT else ScopePoisonF (LetConflict thisMod dups)

  Prod xs -> ProdF $ xs <&> \(i , e) -> (qName2Key (mkQName thisMod i) , Right (e , params))
  Tuple xs -> ProdF $ V.fromList $ Prelude.imap (\i e ->
    (qName2Key (mkQName 0 i) , Right (e , params))) xs

  tt -> Right . (, params) <$> project tt

scopeTT :: Int -> Externs -> ModuleIName -> Params -> TT -> TT
scopeTT tc exts thisMod params tt = apo (scopeApoF tc exts thisMod) (tt , params)
