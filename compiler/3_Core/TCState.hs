{-# LANGUAGE TemplateHaskell #-}

module TCState where

import Prim
import CoreSyn
import Externs
import qualified ParseSyntax as P
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import Control.Lens
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Except
import Control.Monad.ST
import Control.Monad.Primitive
import Data.STRef

type TCEnv s a = StateT (TCEnvState s) (ST s) a
--type TCEnv s a = State (TCEnvState s) a
data TCEnvState s = TCEnvState {
   _pmodule  :: P.Module       -- parsed module

 , _externs :: Externs

 , _wip      :: MV.MVector s Bind
 , _bis      :: MV.MVector s BiSub -- typeVars
 , _domain   :: MV.MVector s BiSub -- Type  -- monotype env
 , _labels   :: MV.MVector s (Maybe Type)
 , _fields   :: MV.MVector s (Maybe Type)
 , _errors   :: [TCError]
 }
makeLenses ''TCEnvState

tcFail e = (errors %= (e:)) *> pure (Fail e)
