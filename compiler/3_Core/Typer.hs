{-# Language TemplateHaskell #-}
module Typer where
{-
import Prim
import Builtins (typeOfLit)
import qualified ParseSyntax as P
import CoreSyn as C
import CoreUtils
import qualified Scope
import Errors
import Externs
import TypeCheck ( check )
import Control.Lens
import Data.Functor.Foldable
import MyString
import qualified Data.Vector as V
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Generic.Mutable as VGM
import qualified Data.Vector.Mutable as MV
import qualified Data.List.NonEmpty as NE
import qualified BitSetMap as BSM ( (!?), fromList, fromVec, singleton, unzip )
import qualified BiUnify (biSubType , BisubEnv , BisubEnvState(..))
import PrettyCore

-- Wanted to somehow pause a hylo to unroll dependencies then resume it.
-- pure unrollBinds issue: "f (Either pauseHylo continue) -> ?"
-- its nonsensical to thread things out then back into the f structure
-- hypoBreak :: (Functor f , Base ff ~ f, Recursive ff) =>
--   (f expr -> expr) -> (seed -> Either modSeed (f (Either ff seed))) -> seed -> Either modSeed expr
-- hypoBreak f g = h where h = fmap (f <<< fmap (_cata f ||| h)) <<< g

-- TODO could free elems of parsebinds faster
data Env = Env { eOpened :: BitSet , eLoadedMods :: (V.Vector LoadedMod) , eModIName :: ModuleIName , eExterns :: Externs , eScopeParams :: Scope.Params , eTopBindsCount :: Int }

-- State that gets dragged through entire Term
data TCEnvState s = TCEnvState
  { blen           :: Int
  , bisubs         :: MV.MVector s BiSub
  , letCaptures    :: BitSet
  , captureRenames :: MV.MVector s Int
  }
type TCEnv s a = StateT (TCEnvState s) (ST s) a

data ModVecSeed = ModVecSeed
 { _inferStack :: NonEmpty IName -- forward refs require pausing current bind
 , _letBinds   :: V.Vector (V.Vector (Either P.FnDef IName))
-- , letNest  :: Int
-- , letBinds :: MV.MVector s (MV.MVector s P.FnDef)

 -- Free vars => any VBruijns from outside the let-binding must be explicitly passed as new VBruijns
 , _tmpFails      :: [TmpBiSubError]    -- bisub failures are dealt with at an enclosing App
-- , _freeLimit   :: Int
-- , _letCaptures :: BitSet
-- , _captureRenames :: MV.MVector s Int -- undef unless letCaptures bit set!
 }; makeLenses ''ModVecSeed

judgeModule :: P.Module -> BitSet -> ModuleIName -> Externs.Externs -> V.Vector LoadedMod -> (ModuleBinds , Errors)
judgeModule pm importedModules modIName exts loaded = let
  letCount = pm ^. P.parseDetails . P.letBindCount
  pBinds = pm ^. P.bindings
  topBindsCount = V.length pBinds
  modOpens = pm ^. P.imports
  scopeParams = Scope.initModParams letCount modOpens importedModules (pBinds <&> (^. P.fnIName))
  env = Env importedModules loaded modIName exts scopeParams topBindsCount
  startSeed = ModVecSeed (0 :| []) (V.singleton (Left <$> pBinds)) []
  (retSeed , modBinds) = constructNSeed (topBindsCount + letCount) (nextBind env) startSeed
  in (modBinds , _errors retSeed)

-- state: rev stack forward refs , (let-nest , bisubs , letCaptures) & errors
nextBind :: Env -> V.Vector (LetMeta , Bind) -> ModVecSeed -> ((LetMeta , Bind) , ModVecSeed)
nextBind env prevRefs seed = let
  parseBindIdx :| fwds = seed ^. inferStack
  perms = mempty :: V.Vector Int
--bindIdx = perms V.! parseBindIdx
  isForwardRef iNm = _ -- (perms V.! iNm) >= V.length prevRefs
  nextInferStack = case fwds of
    []    -> (parseBindIdx + 1) :| []
    h : t -> h :| t
  nextSeed = seed & inferStack .~ nextInferStack
  in case (seed ^. letBinds) V.! 0 V.! parseBindIdx of
  Right bindIdx -> (prevRefs V.! bindIdx , nextSeed) -- scopeApoF returns TTF (Either TT ScopeSeed)
  Left abs -> let
    letIName = mkQName (eModIName env) (abs ^. P.fnIName)
    bindIdx = _
    letMeta bindIdx = LetMeta (V.length (seed ^. letBinds) == 1) letIName
      (VQBindIndex (mkQName (eModIName env) bindIdx)) (abs ^. P.fnSrc)

    scopeApoF = Scope.scopeApoF (eTopBindsCount env) (eExterns env) (eModIName env)
    expr' :: Either ModVecSeed Expr
    expr' = fst $ runST $ runStateT (hypoBreak (infer env) scopeApoF (abs ^. P.fnRhs , eScopeParams env))
      (BiUnify.BisubEnvState _blen _bis [])
    expr = _
    in ((letMeta (V.length prevRefs) , BindOK optInferred expr) , nextSeed)

-- ! tc fails , bisubs , letCaptures aggregate the env!
-- ! Allow inference to stack dependencies, then unroll them later
-- terms and types must be built in lockstep
-- ! cataM: in order to biunify subbranches & insert casts
infer :: forall s. Env -> P.TTF (BiUnify.BisubEnv s Expr) -> BiUnify.BisubEnv s Expr
infer env = \case
-- P.IQVarF q | modName q == eModIName env -> Left (seed & inferStack %~ (unQName q NE.<|))
-- P.VarF (P.VLetBind (_iName , letNest , letIdx , i)) -> _ -- Also P.LabelDeclF: getModBind False letNest letIdx i.
-- P.LetInF block liftNames pInTT -> _

--  P.AppF src f ars -> pure $ App f ars
--  --freshBiSubs 1 >>= \[retV] ->
--  --  (, tyVar retV) <$> bisub fTy (prependArrowArgsTy argTys (tyVar retV))
--
--  P.LitF l -> pure $ Lit l -- Core (Lit l) (TyGround [typeOfLit l])
--  P.ProdF bsm -> _
-}
