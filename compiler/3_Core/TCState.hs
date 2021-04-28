{-# LANGUAGE TemplateHaskell #-}

module TCState where

import CoreSyn
import Externs
import qualified ParseSyntax as P
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import Control.Lens

-- codegen wants to know when it can trim memory pools
-- so our QTT also records the type of use
-- Mode is different for each argument (subexpression) calculated
-- based on what functions do with their args
-- mode is reader, until a label is encountered, when it becomes builder/wrapper
data Mode = Reader | Builder | Wrapper

type TCEnv s a = StateT (TCEnvState s) (ST s) a
data TCEnvState s = TCEnvState {
 -- in
   _pBinds  :: V.Vector P.TopBind -- parsed module
 , _externs :: Externs

 -- out
 , _wip     :: MV.MVector s Bind
 , _errors  :: [TCError]
 , _qtt     :: MV.MVector s QTT -- indexed by argnames, like domain

 -- state
 , _bindWIP :: IName
 , _minTVar :: IName

 , _level   :: Dominion
 , _deBruijn:: MV.MVector s Int

 , _quants  :: Int
 , _mode    :: Mode
 , _bis     :: MV.MVector s BiSub -- typeVars
 , _domain  :: MV.MVector s BiSub -- Type  -- monotype env
 , _labels  :: MV.MVector s (Maybe Type)
 , _fields  :: MV.MVector s (Maybe Type)
 }
makeLenses ''TCEnvState

tcStateLocalMode go = use mode >>= \sv -> go <* (mode .= sv)

tcFail e = (errors %= (e:)) *> pure (Fail e)

-- do a bisub with typevars
withBiSubs :: Int -> (Int->TCEnv s a) -> TCEnv s (a , [Int]) --(a , MV.MVector s BiSub)
withBiSubs n action = do
  bisubs <- use bis
  let biSubLen = MV.length bisubs
      genFn i = let tv = [THVar i] in BiSub [] [] --BiSub tv tv
      tyVars = [biSubLen .. biSubLen+n-1]
  bisubs <- MV.grow bisubs n
  tyVars `forM` \i -> MV.write bisubs i (genFn i)
  level %= (\(Dominion (f,x)) -> Dominion (f,x+n))
  bis .= bisubs
  ret <- action biSubLen
  pure (ret , tyVars)
