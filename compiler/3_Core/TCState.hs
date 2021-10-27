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
 , _thisMod :: ModuleIName -- annotate local labels / types etc

 -- out
 , _wip        :: MV.MVector s Bind
 , _biFails    :: [BiSubError]
 , _scopeFails :: [ScopeError]

 -- state
 , _lvl        :: Int
 , _srcRefs    :: Maybe SrcInfo
 , _tmpFails   :: [TmpBiSubError] -- App local bisub failures
 , _bindWIP    :: IName
 , _deBruijn   :: MV.MVector s Int
 , _quants     :: Int -- fresh names for generalised typevars [A..Z,A1..Z1..]
 , _blen       :: Int
 , _bis        :: MV.MVector s BiSub -- typeVars
 , _deadVars   :: Integer -- bitmask for TVars of shallower let-nests that we mustn't generalize

 , _mus        :: Int -- fresh names for recursive types [x,y,z,x1,y1...]
 , _muNest     :: IntMap (IName , Type)  -- mu bound types deeper in the type that could be merged with
 , _muEqui     :: IntMap IName -- THVars converted to THMuBound (recursive type marker)
 , _liftMu     :: Maybe Type   -- mus constructed inside tycons can often be rolled up to contain the outer tycon

 , _normFields :: VU.Vector IName
 , _normLabels :: VU.Vector IName
}

makeLenses ''TCEnvState

--tcFail e = error $ e -- Poison e _ --(errors %= (e:)) *> pure (Fail e)

dupVar pos x = use bis >>= \v -> MV.modify v
  (\(BiSub p m qp qm) -> if pos then BiSub p m (qp+1) qm else BiSub p m qp (qm+1)) x

dupp pos ty = let dup = dupp in ty `forM` \case
  THVar x -> dupVar pos x
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
  biLen  <- use blen
  let tyVars   = [biLen .. biLen+n-1]
  blen .= (biLen + n)
  bisubs <- MV.grow bisubs n
  bis .= bisubs
  tyVars `forM` \i -> MV.write bisubs i (BiSub [] [] 0 0)
  ret <- action biLen
--tyVars `forM` \i -> MV.write bisubs i (BiSub [] [] 0 0)
  pure (ret , tyVars)
