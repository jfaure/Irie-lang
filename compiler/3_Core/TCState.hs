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

-- Convert QNames to VArgs so bindings can also be beta-reduced optimally
-- Convert VArgs to Lin by inserting Dups
-- this produces an "import signature" for the module

type TCEnv s a = StateT (TCEnvState s) (ST s) a
data TCEnvState s = TCEnvState {
 -- in
   _pBinds      :: V.Vector P.FnDef -- parsed module
 , _externs     :: Externs          -- imported bindings
 , _thisMod     :: ModuleIName      -- used to make the QName for local bindings
 , _openModules :: BitSet

 -- out
 , _wip         :: MV.MVector s Bind
 , _errors      :: Errors

 -- Linearisation
-- , nameMap :: M.Map VName LiName
-- , counts  :: MV.MVector s Int -- count occurences of a LiName, to insert appropriate amount of dups

 , _muInstances :: IM.IntMap Int -- Instantiation of mu-types; not brilliant

 -- Biunification state
 , _bindWIP     :: (IName , Bool)     -- to identify recursion and mutuals (Bool indicates recursion)
 , _tmpFails    :: [TmpBiSubError]    -- bisub failures are dealt with at an enclosing App
 , _blen        :: Int                -- cursor for bis which may have spare space
 , _bis         :: MV.MVector s BiSub -- typeVars
 , _argVars     :: MV.MVector s Int   -- arg IName -> TVar map
   -- (rather than Arg i => TVar i) to trim bisubs more frequently

 -- tvar kinds (see Generalise.hs)
 , _escapedVars :: BitSet  -- TVars of shallower let-nests (don't generalize)
 , _leakedVars  :: BitSet  -- TVars bisubbed with escapedVars
 , _deadVars    :: BitSet  -- formerly leaked now fully captured

 -- Type Analysis phase (Gen + simplification)
 , _recVars     :: Integer -- bitmask for recursive TVars
 , _coOccurs    :: MV.MVector s ([Type] , [Type]) -- (pos , neg) occurs are used to enable simplifications
}; makeLenses ''TCEnvState

-- Generalisation state
type GenEnv s a = StateT (GenEnvState s) (ST s) a
data GenEnvState s = GenEnvState {
   _muWrap      :: [(Int , IName , Type , [InvMu])] -- (recBranch , muVar , muType , startInvMu , curInvMu)
 , _externsGen  :: Externs
 -- ^ several tycon branches may contain a mu type , and a µtype may contain multiple fixpoints
 , _seenVars    :: BitSet
 , _hasRecs     :: BitSet
 , _quants      :: Int  -- fresh names for generalised typevars [A..Z,A1..Z1..]
 , _quantsRec   :: Int  -- fresh names for generalised recursive typevars [x..y,x1..y1..]
 , _biEqui      :: MV.MVector s IName -- TVar -> THBound; complement 0 indicates not gen yet
}; makeLenses ''GenEnvState

clearBiSubs :: Int -> TCEnv s ()
clearBiSubs n = (blen .= n) *> (deadVars .= 0)

-- spawn new tvar slots in the bisubs vector
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
