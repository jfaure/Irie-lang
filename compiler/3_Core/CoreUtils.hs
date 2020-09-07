module CoreUtils where
----------------------------------------------------
-- Various utility functions operating on CoreSyn --
----------------------------------------------------
import Prim
import CoreSyn
import PrettyCore

isArrowTy = \case
  [THArrow{}] -> True
  [THPi (Pi p t)] -> isArrowTy t
  [THSi (Pi p t) _] -> isArrowTy t
  x -> False

getRetTy = \case
  [THArrow _ r] -> getRetTy r -- currying
  [THPi (Pi ps t)] -> getRetTy t
  x -> x

flattenArrowTy ty = let
  go = \case
    [THArrow d r] -> let (d' , r') = go r in (d ++ d' , r')
    t -> ([] , t)
  in (\(ars,r) -> [THArrow ars r]) . go $ ty

tyOfTy t = case t of
  [] -> _
  [THRecSi f ars] -> let
    arTys = take (length ars) $ repeat [THSet 0]
    uni = maximum $ (\case { [THSet n] -> n ; x -> 0 }) <$> arTys
    in [THArrow arTys [THSet uni]]
  [t] -> [THSet 0]
  t  -> error $ "multiple types: " ++ show t

tyOfExpr  = \case
  Core x ty -> ty
  CoreFn _ _ _ ty  -> ty
  ExtFn _nm ty -> ty
  Ty t      -> tyOfTy t
  Fail e    -> []

-- expr2Ty :: _ -> Expr -> TCEnv s Type
-- Expression is a type (eg. untyped lambda calculus is both a valid term and type)
expr2Ty judgeBind e = case e of
 Ty x -> pure x
 Core c ty -> case c of
   Var (VBind x) -> pure [THRec x]
   Var (VArg x)  -> pure [THArg x] -- TODO ?!
   App (Var (VBind fName)) args -> pure [THRecSi fName args]
   x -> error $ "raw term cannot be a type: " ++ show e
 x -> error $ "raw term cannot be a type: " ++ show x

getTypeIndexes = \case
  [THFam t args ixs] -> ixs
  [THRecSi m ixs] -> (`Core` []) <$> ixs
  [THPi (Pi b ty)] -> getTypeIndexes ty
  x -> []

zipWithPad :: a -> b -> (a->b->c) -> [a] -> [b] -> [c]
zipWithPad a b f = go where
  go [] y = zipWith f (repeat a) y
  go x [] = zipWith f x (repeat b)
  go (x:xs) (y:ys) = f x y : go xs ys

mergeIndex :: Expr -> Expr -> Expr
mergeIndex = _
