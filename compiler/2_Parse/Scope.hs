{-# Language TemplateHaskell #-}
module Scope (solveScopesF , initParams , RequiredModules , OpenModules) where -- (solveScopes , solveScopesF) where
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
type ScopeAcc = Params -> (BitSet , TT)
data Params = Params
  { _open        :: OpenModules
  , _req         :: RequiredModules
  , _lets        :: BitSet
  , _args        :: BitSet
  , _bruijnMap   :: V.Vector Int   -- pre-built by mkCase: text IName -> BruijnArg
  , _bruijnCount :: Int -- nesting level
--, _letMap    :: V.Vector IName
  } deriving Show ; makeLenses ''Params

initParams open required = Params open required emptyBitSet emptyBitSet (V.create (MV.new 300)) 0

--solveScopes :: Externs -> ModuleIName -> OpenModules -> RequiredModules -> TT -> TT
--solveScopes e thisMod open required tt = let
--  params = Params emptyBitSet open required emptyBitSet emptyBitSet (V.create $ MV.new 300)-- mempty
--  in snd (cata (solveScopesF e thisMod) tt params)

-- * Track name scopes , free variables and linearity , resolve VExterns to BruijnArg | QName
-- * TODO vars must resolve to let-binds without being inferred at top-level
solveScopesF :: Externs -> ModuleIName -> TTF ScopeAcc -> ScopeAcc
solveScopesF exts thisMod this params = let
--doBruijnAbs :: BruijnAbsF ScopeAcc -> (BitSet , TT)
  doBruijnAbs (BruijnAbsF n bruijnSubs _ tt) = let
    argsSet    = intList2BitSet (fst <$> bruijnSubs)
    warnShadows ret = if
      | (params._args .&. argsSet) /= 0 -> ScopeWarn "λ-binding shadows λ-binding" ret
      | (params._lets .&. argsSet) /= 0 -> ScopeWarn "λ-binding shadows let binding" ret
      | otherwise -> ret
    in tt (params
      & args %~ (.|. argsSet)
      & bruijnCount %~ (+ n)
      & bruijnMap %~ V.modify (\v -> bruijnSubs `forM_` \(i , b) -> MV.write v i (b + params._bruijnCount))
      ) & \(free , body) -> (free , warnShadows $ BruijnLam (BruijnAbsF n [] params._bruijnCount body))
  in case this of
  VarF (VBruijn i) -> (0 `setBit` i , Var (VBruijn i))
  VarF (VExtern i) -> (0 , ) $ if
    | params._args `testBit` i -> Var $ VBruijn (params._bruijnCount - 1 - (params._bruijnMap V.! i))
    | params._lets `testBit` i -> Var $ VQBind (mkQName thisMod i)
    | otherwise -> handleExtern exts thisMod params._open i
  VarF (VQBind q) -> error $ (showRawQName q)
  BruijnLamF b -> doBruijnAbs b
--MatchBF scrut splits d -> let -- Solved case expr
--  go = (\(BruijnLam b) -> b) . snd . doBruijnAbs -- not brilliant
--  in (0 , MatchB (snd $ scrut params) (go <$> splits) (go <$> d))

  -- ! TODO letbounds processed here since must know their enclosing scope - how to resolve later?
  LetBindsF ls tt  -> let
    params2 = params & lets %~ (.|. intList2BitSet (fst <$> ls))
--  ls' = ls <&> \(iNm , BruijnAbsF n subs nest body) -> (iNm , BruijnAbsF n subs nest (snd $ body params2)) -- TOOD 
    ls' = ls <&> \(iNm , body) -> (iNm , (snd $ body params2)) -- TOOD 
    in tt params2 & \(acc , r) -> (acc , LetBinds ls' r) -- to regen them
  JuxtF o args -> let (lins , r) = unzip (distribute args params) in (foldr (.|.) 0 lins , solveMixfixes r)

  -- CasePatF overrides cata via newtype: patterns may contain mixfixes but also introduce arguments once solved
  -- for patterns we need: resolve mixfix externs > solvemixfix > unpattern > solvescopes
  -- * insert a pretraversal of patterns in scope context before patternsToCase and continuing solveScopes
  CasePatF (CaseSplits scrut patBranchPairs) -> let
    solvedBranches :: [(TT , TT)]
    solvedBranches = patBranchPairs <&> \(pat , br) -> let
      clearExtsF = \case
        VarF (VExtern i)
          | params._lets `testBit` i -> Var $ VQBind (mkQName thisMod i)
          | MFExpr m <- handleExtern exts thisMod params._open i -> MFExpr m
          | otherwise -> Var (VExtern i)
        JuxtF o args -> solveMixfixes args
        tt -> embed tt
      in (cata clearExtsF pat , br)
    (this , bruijnSubs@[]) = patternsToCase scrut solvedBranches
    -- proceed with solvescopes using current context
    in cata (solveScopesF exts thisMod) this params

  tt -> let r = distribute tt params in (foldr (.|.) 0 (fst <$> r) , embed (snd <$> r))

-- TODO don't allow `bind = lonemixfixword`
-- handleExtern (readParseExtern open mod e i) ||| readQParseExtern ∷ ExternVar
handleExtern exts mod open i = case readParseExtern open mod exts i of
  ForwardRef b  -> Var (VQBind (mkQName mod b)) -- judgeLocalBind b
  Imported e    -> InlineExpr e
   -- (errors . scopeFails %= s)
  NotOpened m h -> ScopePoison (ScopeNotImported h m)
  NotInScope  h -> ScopePoison (ScopeError h)
  AmbiguousBinding h ms -> ScopePoison (AmbigBind h ms)

  MixfixyVar m  -> MFExpr m -- TODO if ko, mixfix should report "mixfix word cannot be a binding: "
  x -> error (show x)
