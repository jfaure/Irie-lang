{-# LANGUAGE TemplateHaskell #-}
module TCState where
import CoreSyn ( tyBot, tyTop, BiSub(BiSub), Bind, LetMeta )
import qualified Scope (Params)
import Externs
import Errors ( Errors, TmpBiSubError )
import Control.Lens ( use, (.=), makeLenses )
import qualified Data.Vector.Mutable as MV ( MVector, grow, length, write )
import qualified ParseSyntax as P ( FnDef )
import qualified Data.Vector as V ( Vector )

-- inference uses a cataM (biunification vector and new tvar assignments)
type TCEnv s a = StateT (TCEnvState s) (ST s) a
data TCEnvState s = TCEnvState {
 -- in
   _externs     :: Externs     -- vector ExternVars
 , _loadedMs    :: V.Vector LoadedMod
 , _thisMod     :: ModuleIName -- used to make the QName for local bindings
 , _openModules :: BitSet

 -- out
 , _modBinds    :: MV.MVector s (LetMeta , Bind) -- all lets lifted, the P.FnDef is saved in letBinds
 , _letBinds    :: MV.MVector s (MV.MVector s P.FnDef)-- (Either P.FnDef Bind))
 , _letNest     :: Int
 , _errors      :: Errors

 -- Biunification state
 , _topBindsCount :: Int
 , _topBindsMask  :: BitSet
 , _bindsBitSet   :: BitSet -- mark inferred binds
 , _inferStack    :: BitSet -- To detect infer cycles: recursion / mutuals
 , _scopeParams   :: Scope.Params
 , _bruijnArgVars :: V.Vector Int       -- bruijn arg -> TVar map
 , _tmpFails      :: [TmpBiSubError]    -- bisub failures are dealt with at an enclosing App
 , _blen          :: Int                -- cursor for bis which may have spare space
 , _bis           :: MV.MVector s BiSub -- typeVars

 -- Free vars => any VBruijns from outside the let-binding must be explicitly passed as new VBruijns
 , _freeLimit   :: Int
 , _letCaptures :: BitSet
 , _captureRenames :: MV.MVector s Int -- unset unless letCaptures bit set!
}; makeLenses ''TCEnvState

clearBiSubs :: Int -> TCEnv s ()
clearBiSubs n = blen .= n

-- spawn new tvar slots in the bisubs vector
freshBiSubs :: Int -> TCEnv s [Int]
freshBiSubs n = do
  bisubs <- use bis
  biLen  <- use blen
  let tyVars  = [biLen .. biLen+n-1]
  blen .= biLen + n
  bisubs <- if MV.length bisubs < biLen + n then MV.grow bisubs n else pure bisubs
  bis .= bisubs
  tyVars `forM_` \i -> MV.write bisubs i (BiSub tyBot tyTop)
  pure tyVars
