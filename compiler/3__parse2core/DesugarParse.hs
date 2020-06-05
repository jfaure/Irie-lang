module DesugarParse where

import Prim
import CoreSyn
import qualified ParseSyntax as P
import qualified Data.Vector as V
import qualified Data.Map as M
import Control.Monad.State
import Data.Foldable
import Data.Functor
import Debug.Trace

-- output is a list of argument inames and the expression
matches2TT :: [P.FnMatch] -> ([IName] , [[P.TT]] , P.TT) =
  let convPat = \case
        P.PArg i -> (i , [])
        P.PTyped (P.PArg i) ty -> (i , [ty])
        x -> error $ "unknown pattern: " ++ show x
  in \case
    [P.FnMatch impls f e] -> let
      (args , argTys) = unzip $ convPat <$> f
      in (args , argTys , e)
    x -> error $ concatMap show x

--  P.Lit l   -> pure . Right $ case l of
--    PolyInt{}  -> Instr MkNum  [Lit l]
--    PolyFrac{} -> Instr MkReal [Lit l]

resolveInfixes :: (P.TT -> P.TT) -> P.TT -> [(P.TT,P.TT)] -> P.TT
resolveInfixes hasPrec leftExpr infixTrain = let
  -- 1. if rOp has lower prec then lOp then add it to the opStack
  -- 2. else apply infix from the opStack
  -- 3. when no more rOp's, Apply remaining infixes from the opStack
  _ `hasPrec` _ = True -- TODO
  handlePrec :: (P.TT, [(P.TT, P.TT)]) -> (P.TT, P.TT)
             -> (P.TT, [(P.TT, P.TT)])
  handlePrec (expr, []) (rOp, rExp) =
    (P.App rOp [expr, rExp] , [])
  handlePrec (expr, (lOp, lExp) : stack) next@(rOp, _) =
    if lOp `hasPrec` rOp
    then (expr , next : (lOp, lExp) : stack)
    else handlePrec (P.App lOp [expr, lExp] , stack) next
  (expr, remOpStack) = foldl' handlePrec (leftExpr, []) infixTrain

  -- apply remaining opStack
  infix2App lExp (op, rExp) = P.App op [lExp, rExp]
  in foldl' infix2App expr remOpStack
