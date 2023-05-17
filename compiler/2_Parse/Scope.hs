{-# Language TemplateHaskell #-}
module Scope (scopeTT , scopeApoF , initParams , RequiredModules , OpenModules , Params) where
import UnPattern (patternsToCase , Scrut(..))
import ParseSyntax
import QName
import CoreSyn (ExternVar(..)) -- TODO rm
import Mixfix (solveMixfixes)
import Externs ( readParseExtern, Externs )
import Errors
import Data.Functor.Foldable
import Control.Lens
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV

-- * within a module, equivalent HNames map to the same IName
-- * inference of terms needs quick and modular indexing + access to metadata
-- * THProduct uses raw INames (no metadata). machine code fields are sorted on HNames
-- * So Types use a module-global set of INames
-- Letblocks and binds = QName { let number ; bind number }
-- types only need the HNames for pretty printing + don't want to rebind metas etc...

-- replace term (not type) INames with VBruijn and QNames

-- free | dups (↑ occurs ; ↓ tweak abs & rename bruijns)
-- free: count escaped vars used by binder to inc the Abs; patch up during inference
-- dups: cata counts uses (except dependent case-splits)

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
  x -> error (show x)

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
        VarF (VExtern i)
          -- overwrites λ-bounds: x = 3 ; f x = x
          -- TODO how to deal with let-bound labels?
--        | params._lets `testBit` i -> Var $ VLetBind (mkQName thisMod i) -- ?! i
          -- Only inline mixfixes, nothing else, (? mutually bound mixfixes used in pattern)
          | MixfixyVar m <- readParseExtern params._open thisMod exts i -> MFExpr m -- Only inline possible mixfixes
          | otherwise -> Var (VExtern i)
        JuxtF o args -> solveMixfixes o args -- TODO need to solveScope the mixfixes first!
        tt -> embed tt
      in (cata clearExtsF pat , br)
    (this , bruijnSubs) = patternsToCase (scrut{- params-}) (params._bruijnCount) solvedBranches
    in case bruijnSubs of
      [] -> (this , params)
      x  -> error ("non-empty bruijnSubs after case-solve: " <> show x)

  doBruijnAbs :: BruijnAbsF TT -> TTF (Either TT Seed)
  doBruijnAbs (BruijnAbsF n bruijnSubs _ tt) = let
    argsSet    = intList2BitSet (fst <$> bruijnSubs)
    warnShadows ret = let argShadows = params._args .&. argsSet ; letShadows = params._lets .&. argsSet in if
      | argShadows /= 0 -> ScopeWarn ("λ-binding shadows λ-binding: "   <> show (bitSet2IntList argShadows)) ret
      | letShadows /= 0 -> ScopeWarn ("λ-binding shadows let binding: " <> show (bitSet2IntList letShadows)) ret
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
  LamPats args rhs -> patternsToCase Question (params._bruijnCount) [(args , rhs)]
    & fst & \t -> Right . (, params) <$> project t
  LambdaCase (CaseSplits' branches) -> BruijnLamF $ BruijnAbsF 1 [] 0
    $ Right (doCase (Var $ VBruijn 0) branches (params & bruijnCount %~ (1+)))
  CasePat (CaseSplits scrut patBranchPairs) -> doCase scrut patBranchPairs params
    & \(tt , seed) -> RawExprF (Right (tt , seed))

  -- ? mutual | let | rec scopes
  LetIn (Block open letType binds) mtt -> let
    letParams = updateLetParams params (toList (binds <&> _fnIName))
    bindsDone :: V.Vector FnDef
    bindsDone = binds <&> (& fnRhs %~ scopeTT exts thisMod letParams)
    in LetInF (Block open letType bindsDone) (mtt <&> \tt -> Right (tt , letParams))

--Tuple xs -> LetInF (Block True Let (V.fromList xs <&> (scopeTT exts thisMod params))) Nothing

  tt -> Right . (, params) <$> project tt

-- ? local MVector to mark occurences
-- hylo: ↓ replace VExterns
--       ↑ rename vars , solveMixfixes
scopeTT :: Externs -> ModuleIName -> Params -> TT -> TT
scopeTT exts thisMod params tt = apo (scopeApoF exts thisMod) (tt , params)

-- QTT: lets and bruijns have mulitplicity (0 | 1 | ω)
