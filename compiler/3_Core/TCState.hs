{-# LANGUAGE TemplateHaskell #-}

module TCState where

import Prim
import CoreSyn
import qualified ParseSyntax as P
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import Control.Lens
import Control.Monad.Trans.State.Strict
import Control.Monad.ST

-- type TCEnv a s = StateT (TCEnvState s) (ST s) a
type TCEnv a = State TCEnvState a
data TCEnvState = TCEnvState {
   _pmodule  :: P.Module       -- parsed module

 , _noScopes :: V.Vector IName -- resolveScopes
 , _externs  :: V.Vector Expr
 , _wip      :: V.Vector Bind  -- polytype env
 , _biSubs   :: BiSubs         -- typevar  env
 , _polyVars :: Int            -- fresh name for polyvars
 }
makeLenses ''TCEnvState
