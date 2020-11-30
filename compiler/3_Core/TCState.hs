{-# LANGUAGE TemplateHaskell #-}

module TCState where

import Prim
import CoreSyn
import Externs
import qualified ParseSyntax as P
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.IntSet as IS
import Control.Lens
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Except
import Control.Monad.ST
import Control.Monad.Primitive
import Data.STRef

-- codegen wants to know when it can trim memory pools
-- so our QTT also records the type of use
-- Mode is different for each argument (subexpression) calculated
-- based on what functions do with their args
-- mode is reader, until a label is encountered, when it becomes builder/wrapper
data Mode = Reader | Builder | Wrapper

type TCEnv s a = StateT (TCEnvState s) (ST s) a
data TCEnvState s = TCEnvState {
 -- in
   _pmodule :: P.Module       -- parsed module
 , _externs :: Externs

 -- out
 , _wip     :: MV.MVector s Bind
 , _errors  :: [TCError]
 , _qtt     :: MV.MVector s QTT -- indexed by argnames, like domain

 -- state
 , _mode    :: Mode
 , _bis     :: MV.MVector s BiSub -- typeVars
 , _domain  :: MV.MVector s BiSub -- Type  -- monotype env
 , _labels  :: MV.MVector s (Maybe Type)
 , _fields  :: MV.MVector s (Maybe Type)
 }
makeLenses ''TCEnvState

tcStateLocalMode go = use mode >>= \sv -> go <* (mode .= sv)

tcFail e = (errors %= (e:)) *> pure (Fail e)
