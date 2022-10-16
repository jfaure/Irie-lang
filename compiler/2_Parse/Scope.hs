{-# Language TemplateHaskell #-}
module Scope (solveScopesF , initParams , RequiredModules , OpenModules , Params) where
import ParseSyntax
import QName
import CoreSyn (ExternVar(..)) -- TODO rm
import Mixfix (solveMixfixes)
import Externs ( readField, readLabel, readParseExtern, readQParseExtern , Externs )
import Errors
import Data.Distributive
import Data.Functor.Foldable
import Control.Arrow
import Control.Lens
import PrettyCore
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import UnPattern

-- equivalent HNames map to the same IName, now we eliminate them completely in favor of VBruijn and QNames
type OpenModules = BitSet
type RequiredModules = BitSet
type ScopeAcc = Params -> TT
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
  extCount = 300 -- max possible number of let-bindings (should be less due to bruijn args)
  in Params open required emptyBitSet emptyBitSet (V.create (MV.new extCount)) 0 (V.create (MV.new extCount)) 0

-- * Track name scopes , free variables and linearity , resolve VExterns to BruijnArg | QName
solveScopesF :: Externs -> ModuleIName -> TTF ScopeAcc -> ScopeAcc
solveScopesF exts thisMod this params = let
  doBruijnAbs :: BruijnAbsF ScopeAcc -> TT -- (BitSet , TT)
  doBruijnAbs (BruijnAbsF n bruijnSubs _ tt) = let
    argsSet    = intList2BitSet (fst <$> bruijnSubs)
    warnShadows ret = let argShadows = params._args .&. argsSet ; letShadows = params._lets .&. argsSet in if
      | argShadows /= 0 -> ScopeWarn ("λ-binding shadows λ-binding: "   <> show (bitSet2IntList argShadows)) ret
      | letShadows /= 0 -> ScopeWarn ("λ-binding shadows let binding: " <> show (bitSet2IntList letShadows)) ret
      | otherwise -> ret
    in tt (params
      & args %~ (.|. argsSet)
      & bruijnCount %~ (+ n)
      & bruijnMap %~ V.modify (\v -> bruijnSubs `forM_` \(i , b) -> MV.write v i (b + params._bruijnCount))
      ) & \body -> warnShadows $ BruijnLam (BruijnAbsF n [] params._bruijnCount body)

  updateLetParams params bindNms = params
      & lets %~ (.|. intList2BitSet bindNms)
      & letNest %~ (1+)
      & letMap %~ V.modify (\v -> bindNms `iforM_` \i e -> MV.write v e (mkQName params._letNest i))
  in case this of
  VarF (VBruijn i) -> {-(0 `setBit` i ,-} Var (VBruijn i)
  VarF (VExtern i) -> if
    | params._args `testBit` i -> Var $ VBruijn  (params._bruijnCount - 1 - (params._bruijnMap V.! i))
    | params._lets `testBit` i -> Var $ VLetBind (params._letMap V.! i)
    | otherwise -> handleExtern exts thisMod params._open params._letMap i
  VarF (VQBind q) -> ScopePoison (ScopeError $ "Var . VQBind " <> showRawQName q)
  BruijnLamF b -> doBruijnAbs b

  -- ? mutual | let | rec scopes
  LetInF (Block open letType binds) tt -> let
    letParams = updateLetParams params (toList (binds <&> _fnIName))
    bindsDone :: V.Vector FnDef
    bindsDone = binds <&> (& fnRhs %~ (\t -> cata (solveScopesF exts thisMod) t letParams))
    in LetIn (Block open letType bindsDone) (distribute tt letParams)

  -- CasePatF overrides the scopeF cata via newtype: patterns contain mixfixes and introduce arguments
  -- for patterns we need: resolve mixfix externs > solvemixfix > unpattern > solvescopes
  -- * insert a pretraversal of *only* patterns under this scope context, then patternsToCase then resume solveScopes
  CasePatF (CaseSplits scrut patBranchPairs) -> let
    solvedBranches :: [(TT , TT)]
    solvedBranches = patBranchPairs <&> \(pat , br) -> let
      clearExtsF = \case
        VarF (VExtern i)
          | params._lets `testBit` i -> Var $ VLetBind (mkQName thisMod i) -- ?! i
          -- Only inline mixfixes, nothing else, (? mutually bound mixfixes used in pattern)
          | MixfixyVar m <- readParseExtern params._open thisMod exts i -> MFExpr m -- Only inline possible mixfixes
          | otherwise -> Var (VExtern i)
        JuxtF o args -> solveMixfixes args
        tt -> embed tt
      in (cata clearExtsF pat , br)
    (this , bruijnSubs) = patternsToCase scrut solvedBranches
    in case bruijnSubs of
      [] -> cata (solveScopesF exts thisMod) this params -- proceed with solvescopes using current context
      x  -> error ("non-empty bruijnSubs after case-solve: " <> show x)

  JuxtF o args -> solveMixfixes (distribute args params)
  tt -> embed (distribute tt params)

-- TODO don't allow `bind = lonemixfixword`
-- handleExtern (readParseExtern open mod e i) ||| readQParseExtern ∷ ExternVar
handleExtern exts mod open lm i = case readParseExtern open mod exts i of
  ForwardRef b  -> Var (VLetBind (lm V.! b))
  Imported e    -> InlineExpr e
  MixfixyVar m  -> MFExpr m -- TODO if ko, mixfix should report "mixfix word cannot be a binding: "
  -- (errors . scopeFails %= s)
  NotOpened m h -> ScopePoison (ScopeNotImported h m)
  NotInScope  h -> ScopePoison (ScopeError h)
  AmbiguousBinding h ms -> ScopePoison (AmbigBind h ms)
  x -> error (show x)
