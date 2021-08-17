module DesugarParse where

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
