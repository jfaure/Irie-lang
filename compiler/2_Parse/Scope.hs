{-# Language TemplateHaskell #-}
module Scope (scopeTT , scopeApoF , initParams , RequiredModules , OpenModules , Params , letMap , lets) where
import UnPattern (patternsToCase , Scrut(..))
import ParseSyntax
import QName
import CoreSyn(ExternVar(..))
import Mixfix (solveMixfixes)
import Externs ( readParseExtern, Externs )
import Errors
import Data.Functor.Foldable
import Control.Lens
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified BitSetMap as BSM

-- * IConv: each module has its convention for an (HName -> IName) isomorphism
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

  , _letMap      :: V.Vector QName -- text IName -> LetName
  , _letNest     :: Int
  } deriving Show ; makeLenses ''Params

initParams open required = let
  sz = 300 -- TODO max number of let-bindings or bruijnVars
  in Params open required emptyBitSet emptyBitSet (V.create (MV.new sz)) 0 (V.create (MV.new sz)) 0

-- TODO don't allow `bind = lonemixfixword`
-- handleExtern (readParseExtern open mod e i) ||| readQParseExtern :: ExternVar
handleExtern :: Externs -> Int -> BitSet -> V.Vector QName -> Int -> TT
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

-- Patterns (- TTs) need their labels and constants scoped, then introduce new args
-- - A (B a _) C
--   .. 
-- + \s0 => guard s0 A \s1 => guard s1 B \s2 s3 => name s2 = a => guard s3 C => rhs
-- = \s0 => case s0 of { A s1 => case s1 of { B (s2=a) s3 => case s3 of { C => rhs }}}
--   if fail at any point, move into next case
-- The recursion scheme: depth first unroll a case-nest to check all guards; but support failure continuation
--unPattern :: Params -> Externs -> ModuleIName -> TT -> TT -> TTF TT
--unPattern params exts thisMod koBranch = \case
--  Var (VExtern i) -> case readParseExtern params._open thisMod exts i of
--    MixfixyVar m  -> MFExprF m -- Only handle mixfixes in case i was overshadowed by an arg
--    ImportLabel q -> QLabelF q
--    _ -> VarF (VExtern i)
--  Juxt o args -> unPattern params exts thisMod koBranch (solveMixfixes o args) -- solvescopes first?
--
--  Label i subPats -> GuardLabelF (mkQName thisMod i) subPats -- new VBruijns , new VExterns -> VBruijns
--  QLabel q    -> GuardLabelF q []
--  ArgProd arg -> GuardArgF arg
--  Tuple args  -> GuardTupleF args
--  x -> DesugarPoisonF (IllegalPattern (show x))
--  unConsArgs = [qName2Key (mkQName 0 i) | i <- [0 .. n-1]] <&> \k -> TupleIdx k scrut

-- Patterns are either case-label or case (eq C x)
unfoldCase :: TT -> [([TT] , TT)] -> Params -> Seed
unfoldCase scrut alts params = _unPattern 

-- * name scope , free variables , dup nodes , resolve VExterns to BruijnArg | QName
-- unpattern assigns debruijn levels: bl, the debruijn index is lvl - bl - 1
type Seed = (TT , Params)
scopeApoF :: Externs -> ModuleIName -> Seed -> TTF (Either TT Seed)
scopeApoF exts thisMod (this , params) = let
  -- Cases require different approach: resolve mixfix externs > solvemixfix > unpattern > solvescopes
  -- * insert a pretraversal of *only* patterns under this scope context, then patternsToCase then resume solveScopes
  doCase :: UnPattern.Scrut -> [(TT, TT)] -> Params -> Seed
  doCase scrut patBranchPairs params = let
    solvedBranches :: [(TT , TT)]
    solvedBranches = patBranchPairs <&> \(pat , br) -> let
      -- Special treatment for Terms in pattern position: we need to find and resolve mixfix labels immediately
      clearExtsF = \case
        VarF (VExtern i) ->
          -- overwrites λ-bounds: x = 3 ; f x = x
          -- TODO how to deal with let-bound labels?
--        | params._lets `testBit` i -> Var $ VLetBind (mkQName thisMod i) -- ?! i
          -- Only inline mixfixes, nothing else, (? mutually bound mixfixes used in pattern)
          case readParseExtern params._open thisMod exts i of
            MixfixyVar m  -> MFExpr m -- Only inline possible mixfixes
            ImportLabel q -> QLabel q
            _ -> Var (VExtern i)
        JuxtF o args -> solveMixfixes o args -- TODO need to solveScope the mixfixes first!
        tt -> embed tt
      in (cata clearExtsF pat , br) -- TODO could ana this so it could fuse
    (this , bruijnSubs) = patternsToCase thisMod (scrut{- params-}) (params._bruijnCount) solvedBranches
    in case bruijnSubs of
      [] -> (this , params)
      x  -> error ("non-empty bruijnSubs after case-solve: " <> show x)

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

  updateLetParams params bindNms = params
    & lets %~ (.|. intList2BitSet bindNms)
    & letNest %~ (1+)
    & letMap %~ V.modify (\v -> bindNms `iforM_` \i e -> MV.write v e (mkQName params._letNest i))
  resolveExt i = if
    | params._args `testBit` i -> Var $ VBruijn  (params._bruijnCount - 1 - (params._bruijnMap V.! i))
    | params._lets `testBit` i -> Var $ VLetBind (params._letMap V.! i)
    | otherwise -> handleExtern exts thisMod params._open params._letMap i
  in case {-d_ (embed $ Question <$ this) $-} this of
  Var v -> case v of
    VBruijnLevel i -> VarF (VBruijn $ params._bruijnCount - 1 - i) -- Arg-prod arg name
    VBruijn 0 -> VarF (VBruijn 0) -- spawned by LambdaCaseF
    VBruijn n -> error "VBruijn n/=0 shouldn't be possible"
    VExtern i -> Left <$> project (resolveExt i)
    VLetBind _-> VarF v
  -- TODO Not ideal; shortcircuits the apomorphism (perhaps. should rework cataM inferF)
  AppExt i args -> Left <$> project (solveMixfixes 0 $ resolveExt i : (scopeTT exts thisMod params <$> args))
  Juxt o args   -> Left <$> project (solveMixfixes o $ scopeTT exts thisMod params <$> args)
  BruijnLam b -> doBruijnAbs b
  LamPats args rhs -> patternsToCase thisMod Question (params._bruijnCount) [(args , rhs)]
    & fst & \t -> Right . (, params) <$> project t
  LambdaCase (CaseSplits' branches) -> BruijnLamF $ BruijnAbsF 1 [] 0
    $ Right (doCase (Var $ VBruijn 0) branches (params & bruijnCount %~ (1+)))
  CasePat (CaseSplits scrut patBranchPairs) -> RawExprF (Right (doCase scrut patBranchPairs params))

  -- ? mutual | let | rec scopes
  LetIn (Block open letType binds) mtt -> let
    letParams = updateLetParams params (toList (binds <&> _fnIName))
    bindsDone :: V.Vector FnDef
    bindsDone = binds <&> (& fnRhs %~ scopeTT exts thisMod letParams)
    in LetInF (Block open letType bindsDone) (mtt <&> \tt -> Right (tt , letParams))

  Prod xs -> ProdF $ xs <&> \(i , e) -> (qName2Key (mkQName thisMod i) , Right (e , params))
  Tuple xs -> ProdF $ V.fromList $ Prelude.imap (\i e ->
    (qName2Key (mkQName 0 i) , Right (e , params))) xs

  tt -> Right . (, params) <$> project tt

scopeTT :: Externs -> ModuleIName -> Params -> TT -> TT
scopeTT exts thisMod params tt = apo (scopeApoF exts thisMod) (tt , params)
