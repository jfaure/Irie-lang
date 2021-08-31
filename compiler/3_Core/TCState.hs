{-# LANGUAGE TemplateHaskell #-}
module TCState where
import CoreSyn
import Externs
import qualified ParseSyntax as P
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Mutable as MV
import Control.Lens

type TCEnv s a = StateT (TCEnvState s) (ST s) a
data TCEnvState s = TCEnvState {
 -- in
   _pBinds  :: V.Vector P.TopBind -- parsed module
 , _externs :: Externs

 -- out
 , _wip        :: MV.MVector s Bind
 , _biFails    :: [BiSubError]
 , _scopeFails :: [ScopeError]

 -- state
 , _srcRefs  :: Maybe SrcInfo
 , _tmpFails :: [TmpBiSubError] -- App local bisub failures
 , _bindWIP  :: IName
 , _level    :: Dominion
 , _deBruijn :: MV.MVector s Int
 , _quants   :: Int
 , _mus      :: Int
 , _bis      :: MV.MVector s BiSub -- typeVars
 , _muEqui   :: IntMap IName -- equivalence classes for mu types, + -> -

 , _normFields :: VU.Vector IName
 , _normLabels :: VU.Vector IName

-- , _labels   :: MV.MVector s (Maybe Type)
-- , _fields   :: MV.MVector s (Maybe Type)
}

makeLenses ''TCEnvState

--tcFail e = error $ e -- Poison e _ --(errors %= (e:)) *> pure (Fail e)

dupVar pos x = use bis >>= \v -> MV.modify v
    (\(BiSub p m qp qm) -> if pos then BiSub p m (qp+1) qm else BiSub p m qp (qm+1)) x

dupp p pos ty = let dup = dupp p in ty `forM` \case
  THVar x | x /= p -> dupVar pos x
--THVar x -> dupVar pos x
--THArrow ars x -> void $ (dup (not pos) `mapM` ars) *> dup pos x
  THTyCon t -> case t of
    THArrow ars x -> void $ (dup (not pos) `mapM` ars) *> dup pos x
    THTuple   tys -> dup pos `traverse_` tys
    THProduct tys -> dup pos `traverse_` tys
    THSumTy   tys -> dup pos `traverse_` tys
  THBi b ty -> void $ dup pos ty
  THMu b ty -> void $ dup pos ty
  x -> pure ()

-- do a bisub with typevars
withBiSubs :: Int -> (Int->TCEnv s a) -> TCEnv s (a , [Int]) --(a , MV.MVector s BiSub)
withBiSubs n action = do
  bisubs <- use bis
  let biSubLen = MV.length bisubs
      genFn i = let tv = [THVar i] in BiSub [] [] 0 0
      tyVars = [biSubLen .. biSubLen+n-1]
  bisubs <- MV.grow bisubs n
  tyVars `forM` \i -> MV.write bisubs i (genFn i)
  level %= (\(Dominion (f,x)) -> Dominion (f,x+n))
  bis .= bisubs
  ret <- action biSubLen
  pure (ret , tyVars)
