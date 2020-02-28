{-# LANGUAGE TemplateHaskell #-}

module TCState where

import CoreSyn
import qualified ParseSyntax as P
import qualified Data.Vector as V
import Control.Lens
import Control.Monad.Trans.State.Strict

type TCEnv a = State TCEnvState a
data TCEnvState = TCEnvState {
   _pmodule:: P.Module -- we are most interested in the bindings
 , _biSubs :: BiSubs   -- typevar  env
 , _wip    :: V.Vector Bind
 }
makeLenses ''TCEnvState
