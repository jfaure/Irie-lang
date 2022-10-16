{-# LANGUAGE TemplateHaskell #-}
module TCState where
import CoreSyn ( tyBot, tyTop, BiSub(BiSub), Bind, Type )
import Externs ( Externs )
import Errors ( Errors, TmpBiSubError )
import Control.Lens ( use, (.=), makeLenses )
import qualified Data.Vector.Mutable as MV ( MVector, grow, length, write )
import qualified ParseSyntax as P ( FnDef )
import qualified Data.Vector as V ( Vector )

-- Convert QNames to VArgs so bindings can also be beta-reduced optimally
-- Convert VArgs to Lin by inserting Dups
-- this produces an "import signature" for the module
type TCEnv s a = StateT (TCEnvState s) (ST s) a
data TCEnvState s = TCEnvState {
 -- in
   _externs     :: Externs     -- imported bindings
 , _thisMod     :: ModuleIName -- used to make the QName for local bindings
 , _openModules :: BitSet

 -- out
 , _wip         :: MV.MVector s (Either P.FnDef Bind)
 , _letBinds    :: MV.MVector s (MV.MVector s (Either P.FnDef Bind))
 , _letNest     :: Int
 , _errors      :: Errors

 -- Biunification state
 , _bruijnArgVars :: V.Vector Int    -- bruijn arg -> TVar map
 , _bindWIP       :: (IName , Bool)     -- to identify recursion and mutuals (Bool indicates recursion)
 , _tmpFails      :: [TmpBiSubError]    -- bisub failures are dealt with at an enclosing App
 , _blen          :: Int                -- cursor for bis which may have spare space
 , _bis           :: MV.MVector s BiSub -- typeVars

 -- tvar kinds (see Generalise.hs)
 , _escapedVars :: BitSet -- TVars of shallower let-nests
 , _leakedVars  :: BitSet -- TVars bisubbed with escapedVars
 , _deadVars    :: BitSet -- formerly leaked now fully captured
}; makeLenses ''TCEnvState

clearBiSubs :: Int → TCEnv s ()
clearBiSubs n = (blen .= n) *> (deadVars .= 0)

-- spawn new tvar slots in the bisubs vector
freshBiSubs :: Int → TCEnv s [Int]
freshBiSubs n = do
  bisubs <- use bis
  biLen  <- use blen
  let tyVars  = [biLen .. biLen+n-1]
  blen .= (biLen + n)
  bisubs <- if MV.length bisubs < biLen + n then MV.grow bisubs n else pure bisubs
  bis .= bisubs
  tyVars `forM_` \i → MV.write bisubs i (BiSub tyBot tyTop)
  pure tyVars
