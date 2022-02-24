{-# LANGUAGE TemplateHaskell #-}
module TCState where
import CoreSyn
import CoreUtils
import Errors
import Externs
import qualified ParseSyntax as P
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.IntMap as IM
import Control.Lens

type TCEnv s a = StateT (TCEnvState s) (ST s) a
data TCEnvState s = TCEnvState {
 -- in
   _pBinds  :: V.Vector P.TopBind -- parsed module
 , _externs :: Externs            -- imported bindings
 , _thisMod :: ModuleIName        -- used to make the QName for local bindings

 -- out
 , _wip         :: MV.MVector s Bind
 , _biFails     :: [BiSubError] -- inference failure
 , _scopeFails  :: [ScopeError] -- name not in scope
 , _checkFails  :: [CheckError] -- type annotation doesn't subsume the inferred one

 -- Instantiation
 , _muInstances :: IM.IntMap Int -- not brilliant

 -- Biunification state
 , _bindWIP     :: IName              -- to identify recursion and mutuals
 , _tmpFails    :: [TmpBiSubError]    -- bisub failures are dealt with at an enclosing App
 , _blen        :: Int                -- cursor for bis which may have spare space
 , _bis         :: MV.MVector s BiSub -- typeVars
 , _argVars     :: MV.MVector s Int   -- arg IName -> TVar map
   -- (rather than Arg i => TVar i) to trim bisubs more frequently

 -- tvar kinds (see Generalise.hs)
 , _escapedVars :: BitSet  -- TVars of shallower let-nests (don't generalize)
 , _leakedVars  :: BitSet  -- TVars bisubbed with escapedVars
 , _deadVars    :: BitSet  -- formerly leaked now fully captured

 -- Generalisation state
 , _muWrap      :: Maybe (IName , Type , [InvMu] , [InvMu])
 , _hasRecs     :: BitSet
 , _quants      :: Int  -- fresh names for generalised typevars [A..Z,A1..Z1..]
 , _quantsRec   :: Int  -- fresh names for generalised recursive typevars [x..y,x1..y1..]
 , _biEqui      :: MV.MVector s IName -- TVar -> THBound; complement 0 indicates not gen yet

 -- Type Analysis phase (Gen + simplification)
 , _recVars     :: Integer -- bitmask for recursive TVars
 , _coOccurs    :: MV.MVector s ([Type] , [Type]) -- (pos , neg) occurs are used to enable simplifications
}

makeLenses ''TCEnvState

--tcFail e = error $ e -- Poison e _ --(errors %= (e:)) *> pure (Fail e)

clearBiSubs :: Int -> TCEnv s ()
clearBiSubs n = (blen .= n) *> (deadVars .= 0)

-- spawn new tvars slots in the bisubs vector
freshBiSubs :: Int -> TCEnv s [Int]
freshBiSubs n = do
  bisubs <- use bis
  biLen  <- use blen
  let tyVars  = [biLen .. biLen+n-1]
  blen .= (biLen + n)
  bisubs <- if MV.length bisubs < biLen + n then MV.grow bisubs n else pure bisubs
  bis .= bisubs
  tyVars `forM` \i -> MV.write bisubs i (BiSub tyBot tyTop)
  pure tyVars
