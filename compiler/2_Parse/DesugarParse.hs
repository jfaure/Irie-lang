module DesugarParse where

import CoreSyn
import qualified ParseSyntax as P

-- output is a list of argument inames and the expression
matches2TT :: [P.FnMatch] -> ([IName] , [[P.TT]] , P.TT) =
  let convPat = \case
        P.PArg i -> (i , [])
        P.PTT (P.Var (P.VLocal i)) -> (i , [])
--      P.PTyped (P.PArg i) ty -> (i , [ty])
        x -> error $ "unknown pattern: " ++ show x
  in \case
    [P.FnMatch impls f e] -> let
      hackApp [P.PApp i ars] = i : ars -- TODO rm this (fix parser)
      hackApp x = x
      (args , argTys) = unzip $ convPat <$> (hackApp f)
      in (args , argTys , e)
    x -> error $ concatMap show x

--  P.Lit l   -> pure . Right $ case l of
--    PolyInt{}  -> Instr MkNum  [Lit l]
--    PolyFrac{} -> Instr MkReal [Lit l]

resolveInfixes :: (P.TT -> P.TT -> Bool) -> P.TT -> [(P.TT,P.TT)] -> P.TT
resolveInfixes hasPrec leftExpr infixTrain = let
  -- 1. if rOp has lower prec then lOp then add it to the opStack
  -- 2. else apply infix from the opStack
  -- 3. when no more rOp's, Apply remaining infixes from the opStack
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
