module DesugarParse (matches2TT , patterns2TT) where
import qualified ParseSyntax as P
import Data.List (unzip3)

--type ArgTys = [[P.TT]]
-- output is a list of argument inames and the expression
matches2TT isTop = \case -- :: [P.FnMatch] -> ([IName] , ArgTys , P.Pattern) =
  [P.FnMatch impls pats e] -> patterns2TT isTop pats e
  x -> error $ "todo equational fn matches: " <> concatMap show x

patterns2TT isTop pats e = let
  (args , argTys , e') = unzip3 $ convPat isTop <$> pats
  e'' = foldl (\b -> maybe b ($ b)) e e'
  in (args , argTys , e'')

convPat :: Bool -> P.Pattern -> (IName , [a] , Maybe (P.TT -> P.TT))
convPat isTop = \case
  P.PArg  i     -> (i , [] , Nothing)
  P.PComp i pat -> (i , [] ,) . Just $ let
    thisArg = P.Var (if isTop then P.VBind i else P.VLocal i)
    in case pat of
    P.PLabel l pats -> \t -> P.App (P.Match [(l , 0 , pats , t)] Nothing) [thisArg]
    P.PTuple  fields -> \t -> let
    -- Note uses negative numbers to indicate tuple indexing
      mkProj l (P.PArg i) = (i , P.TTLens 0 thisArg [l] P.LensGet) -- (i , P.Idx thisArg l)
      mkProj _ p = error $ "not ready for patterns within tuples" <> show p
      (fieldArgs , projs) = unzip $ zipWith mkProj [-1,-2..] fields
      fArgs = P.PArg <$> fieldArgs
      abs = P.Abs (P.FunBind (P.FnDef "tupleProj" False P.Let Nothing [] 0 [P.FnMatch [] fArgs t] Nothing))
      in P.App abs projs

    P.PCons  fields -> \t -> let
      mkProj (l , P.PArg i) = (i , P.TTLens 0 thisArg [l] P.LensGet)
      mkProj p = error $ "not ready for patterns within records" <> show p
      (fieldArgs , projs) = unzip $ mkProj <$> fields
      fArgs = P.PArg <$> fieldArgs
      abs  = P.Abs (P.FunBind (P.FnDef "patProj" False P.Let Nothing [] 0 [P.FnMatch [] fArgs t] Nothing))
      in P.App abs projs
    x -> error $ "not ready for pattern: " <> show x
--    P.Literal l    -> _
--  P.PTT (P.Var (P.VLocal i)) -> (i , [])
--  P.PTyped (P.PArg i) ty -> (i , [ty])
  x -> error $ "unknown pattern: " <> show x
