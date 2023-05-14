{-# LANGUAGE TemplateHaskell #-}
module TCState where
import CoreSyn ( tyBot, tyTop, BiSub(BiSub), Bind )
import Externs ( Externs )
import Errors ( Errors, TmpBiSubError )
import Control.Lens ( use, (.=), makeLenses )
import qualified Data.Vector.Mutable as MV ( MVector, grow, length, write )
import qualified ParseSyntax as P ( FnDef )
import qualified Data.Vector as V ( Vector )

-- inference uses a cataM
type TCEnv s a = StateT (TCEnvState s) (ST s) a
data TCEnvState s = TCEnvState {
 -- in
   _externs     :: Externs     -- imported bindings
 , _thisMod     :: ModuleIName -- used to make the QName for local bindings
 , _openModules :: BitSet

 -- out
 , _letBinds    :: MV.MVector s (MV.MVector s (Either P.FnDef Bind))
 , _letNest     :: Int
 , _errors      :: Errors

 -- Biunification state
 , _bindStack     :: [(Int , Int)]
 , _bruijnArgVars :: V.Vector Int       -- bruijn arg -> TVar map
 , _tmpFails      :: [TmpBiSubError]    -- bisub failures are dealt with at an enclosing App
 , _blen          :: Int                -- cursor for bis which may have spare space
 , _bis           :: MV.MVector s BiSub -- typeVars
 , _lvls          :: [BitSet] -- tvar let-nest scope (see Generalise.hs)

 -- Free vars => any VBruijns from outside the let-binding must be explicitly passed as new VBruijns
 , _freeLimit   :: Int
 , _letCaptures :: BitSet

 -- Type analysis
 , _recursives :: BitSet
 , _nquants :: Int
 , _genVec  :: MV.MVector s Int
}; makeLenses ''TCEnvState

clearBiSubs :: Int -> TCEnv s ()
clearBiSubs n = blen .= n

-- spawn new tvar slots in the bisubs vector
freshBiSubs :: Int -> TCEnv s [Int]
freshBiSubs n = do
  bisubs <- use bis
  biLen  <- use blen
  let tyVars  = [biLen .. biLen+n-1]
  blen .= (biLen + n)
  bisubs <- if MV.length bisubs < biLen + n then MV.grow bisubs n else pure bisubs
  bis .= bisubs
  tyVars `forM_` \i -> MV.write bisubs i (BiSub tyBot tyTop)
  pure tyVars
