{-# Language TemplateHaskell #-}
module Scope (scopeTT , scopeApoF , initModParams , RequiredModules , OpenModules , Params , letMap , lets) where
import ParseSyntax
import QName
import CoreSyn(ExternVar(..) , VName(VQBind))
import Mixfix (solveMixfixes)
import Externs ( readParseExtern, Externs )
import Errors
import Data.Functor.Foldable
import Control.Lens
import Data.List (span)
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified BitSetMap as BSM

-- * IConv: each module has its own isomorpism convention (HName <-> IName)
-- * QName is thus a module name (indicating the IConv) and an IName
-- ? QTT requires cata to track mulitplicity (0 | 1 | ω)
type OpenModules = BitSet
type RequiredModules = BitSet
data Params = Params
  { _open        :: OpenModules
  , _req         :: RequiredModules
  , _lets        :: BitSet
  , _args        :: BitSet
  , _bruijnMap   :: V.Vector Int -- pre-built by mkCase: text IName -> BruijnArg TODO merge with letMap
  , _bruijnCount :: Int -- nesting level
  , _letMap      :: V.Vector (QName , IName) -- letName (letNest , index) & lifted index in module binds
  , _letNest     :: Int
  } deriving Show ; makeLenses ''Params

initParams open required = let
  sz = 2048 -- TODO max number of let-nests and / or bruijn args
  in Params open required emptyBitSet emptyBitSet (V.create (MV.new sz)) 0 (V.create (MV.new sz)) 0

initModParams open required bindNms = initParams open required & \params -> params
  & lets %~ (.|. intList2BitSet bindNms)
  & letNest %~ (1+)
  & letMap %~ V.modify (\v -> bindNms `iforM_` \i e -> MV.write v e (mkQName 0 i , i)) -- top-binds written to modBinds without offset

-- TODO don't allow `bind = lonemixfixword`
-- handleExtern (readParseExtern open mod e i) ||| readQParseExtern :: ExternVar
handleExtern :: Externs -> Int -> BitSet -> V.Vector _ -> Int -> TT
handleExtern exts mod open lm i = case readParseExtern open mod exts i of
  ForwardRef b  -> Var (VLetBind (lm V.! b))
  Imported e    -> InlineExpr e
  MixfixyVar m  -> MFExpr m -- TODO if ko, mixfix should report "mixfix word cannot be a binding: "
  -- (errors . scopeFails %= s)
  NotOpened m h -> ScopePoison (ScopeNotImported h m)
  NotInScope  h -> ScopePoison (ScopeError h)
  AmbiguousBinding h ms -> ScopePoison (AmbigBind h ms)
  ImportLabel q -> QLabel q
  x -> error (show x)

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
  doBruijnAbs :: BruijnAbsF TT -> TTF (Either TT Seed)
  doBruijnAbs (BruijnAbsF n bruijnSubs _ tt) = let
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
      MV.write v e (mkQName params._letNest i , i + topBindsCount + liftName))
  resolveExt i = if
    | params._args `testBit` i -> Var $ VBruijn  (params._bruijnCount - 1 - (params._bruijnMap V.! i))
    | params._lets `testBit` i -> Var $ VLetBind (params._letMap V.! i)
    | otherwise -> handleExtern exts thisMod params._open params._letMap i

  -- Patterns (- TTs) need their labels and constants scoped, then introduce new args
  -- - A (B a _) C => rhs1
  --   _  => rhs2
  -- + \s0 => guard s0 A \s1 => guard s1 B \s2 s3 => name s2 = a => guard s3 C => rhs
  -- = \s0 => case s0 of { A s1 => case s1 of { B (s2=a) s3 => case s3 of { C => rhs }}}
  -- failures : redundant pattern match / illegal pattern
  -- Case /guard failures are recoverable iff wildcard higher case next: this duplicates rhs
  -- ! This delegates spawning of new VBruijns via GuardArgs
  unfoldCase :: TT -> [((TT {-, [TT]-}) , TT)] -> Params -> TT
  unfoldCase scrut rawAlts params = let
    scopeLayer pat = case pat of
      Var (VExtern i) -> case readParseExtern params._open thisMod exts i of
        ImportLabel q -> QLabel q
  --    ImportLit
        _ -> Var (VExtern i) -- new argument
      Juxt o args -> solveMixfixes o (scopeLayer <$> args) -- TODO need to solveScope VExterns first
      tt -> tt
    isLabel = \case { QLabel{} -> True ; Label{} -> True ; App{} -> True; _ -> False }
    (altPats , rest) = span (isLabel . fst) (first scopeLayer <$> rawAlts)
    alts = altPats <&> \(pat {-, guards)-} , rhs) -> case pat of
      QLabel q -> (qName2Key q , rhs) -- Guards openMatch guards rhs)
      Label i subPats -> (qName2Key (mkQName thisMod i) , GuardArgs subPats rhs)
      App (QLabel q) subPats -> (qName2Key q , GuardArgs subPats rhs)
      x -> (0 , ScopePoison (ScopeError $ "bad pattern: " <> show x))
    openMatch = case rest of -- TODO could be guarded; another case
      [] -> Nothing
      (WildCard , rhs) : redundant -> Just rhs -- guards
      x -> error (show x) -- _illegallPattern -- argProd , Tuple , Lit are parsed as guards
    -- branch = mkBruijnLam (BruijnAbsF n argSubs 0 rhs)
    match = MatchB scrut (BSM.fromList alts) openMatch
   in match -- (if null redundant then identity else ScopeWarn RedundantPatMatch) (match (Just wild))

  -- Spawn new VBruijns and Guard them if further cases required
  -- a guard is recoverable if an enclosing case has a wildcard
  -- nestGuards: enclosing guards on top of subpatterns for these args
  guardArgs [] rhs [] = RawExprF (Right (rhs , params))
  guardArgs args rhs nestGuards = let -- TODO use the fallback (happens when labels are matched..)
    n = length args
    lvl = params._bruijnCount :: Int
    vbruijnLvls = [lvl .. lvl + n-1] -- [n-1 , n-2 .. 0]
    argSubs = let getArgSub i = \case { Var (VExtern e) -> [(e , i)] ; x -> [] }
      in concat (zipWith getArgSub vbruijnLvls args)
    mkGuards pat vbl = case pat of
      Var VExtern{} -> []
      WildCard{} -> []
      pat -> [GuardPat pat (Var (VBruijnLevel vbl))]
    guards = concat (zipWith mkGuards args vbruijnLvls) :: [Guard]
    in doBruijnAbs $ BruijnAbsF n argSubs 0 (Guards Nothing (guards ++ nestGuards) rhs)

  in case {-d_ (embed $ Question <$ this) -} this of
  Var v -> case v of
    VBruijnLevel i -> VarF (VBruijn $ params._bruijnCount - 1 - i) -- Arg-prod arg name
    VBruijn n -> VarF (VBruijn n) -- lambdaCaseF spawns (VBruijn 0) ; error "VBruijn n/=0 shouldn't be possible"
    VExtern i -> Left <$> project (resolveExt i)
  -- TODO Not ideal; retype solvemixfix on (∀a. TTF a) ?
  Juxt o args   -> Left <$> project (solveMixfixes o $ scopeTT topBindsCount exts thisMod params <$> args)
--Juxt o args   -> scopeApoF exts thisMod . (,params) $ solveMixfixes o $ _ $
--  args <&> \case { Var v -> handleVar v ; x -> Left <$> project x }
  BruijnLam b -> doBruijnAbs b
  LambdaCase (CaseSplits' alts) -> doBruijnAbs $ BruijnAbsF 1 [] 0 (CasePat (CaseSplits (Var (VBruijn 0)) alts))
  CasePat (CaseSplits scrut alts) -> RawExprF (Right (unfoldCase scrut alts params , params))

  -- v transpose ?
  FnEqns eqns -> case eqns of
    [GuardArgs pats rhs] -> guardArgs pats rhs []
  GuardArgs pats rhs -> guardArgs pats rhs []
  Guards _ko [] rhs -> scopeApoF topBindsCount exts thisMod (rhs , params) -- RawExprF (Right (rhs , params)) -- skip
  Guards ko (g : guards) rhs -> let
    guardLabel scrut q subPats = fmap (Right . (,params)) $ let
      rhs' = if null subPats then Guards ko guards rhs else GuardArgs subPats (Guards ko guards rhs)
      in MatchBF scrut (BSM.singleton (qName2Key q) rhs') ko
    in case g of
    GuardPat pat scrut -> case pat of
      Label l subPats -> guardLabel scrut (mkQName thisMod l) subPats
      Tuple subPats -> let
        n = length subPats
        projections = [TupleIdx (qName2Key (mkQName 0 i)) scrut | i <- [0 .. n - 1]]
        in Right . (,params) <$> AppF (GuardArgs subPats (Guards ko guards rhs)) projections
      -- vv TODO could be Label or new arg
      Var (VExtern i) -> case readParseExtern params._open thisMod exts i of
        ImportLabel q -> guardLabel scrut q []--guards
        NotInScope _  -> doBruijnAbs (BruijnAbsF 1 [(i , params._bruijnCount)] 0 rhs)
        x -> DesugarPoisonF (IllegalPattern ("Ext: " <> show x))
      x -> DesugarPoisonF (IllegalPattern (show x))
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
    in if dups == 0 then letTT else ScopePoisonF (LetConflict (show <$> bitSet2IntList dups))

  Prod xs -> ProdF $ xs <&> \(i , e) -> (qName2Key (mkQName thisMod i) , Right (e , params))
  Tuple xs -> ProdF $ V.fromList $ Prelude.imap (\i e ->
    (qName2Key (mkQName 0 i) , Right (e , params))) xs

  tt -> Right . (, params) <$> project tt

scopeTT :: Int -> Externs -> ModuleIName -> Params -> TT -> TT
scopeTT tc exts thisMod params tt = apo (scopeApoF tc exts thisMod) (tt , params)
