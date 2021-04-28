module CoreUtils where
----------------------------------------------------
-- Various utility functions operating on CoreSyn --
----------------------------------------------------
import CoreSyn
import ShowCore()
import Data.List
import qualified Data.IntMap as IM
--import qualified Data.Vector as V
--import qualified Data.IntSet as IS

-- substitute all pi bound variables for new typevars
-- TODO record and sum type also
substFreshTVars tvarStart ty = let
  r = substFreshTVars tvarStart
  in case ty of
  [THBound i] -> [THVar (tvarStart + i)]
  [THArrow as ret] -> [THArrow (r <$> as) (r ret)]
  [t] -> [t]

addArrowArgs [] = identity
addArrowArgs args = \case
  [THArrow as r] -> [THArrow (as ++ args) r]
  [THPi (Pi p t)]   -> [THPi (Pi p $ addArrowArgs args t)]
  [THSi (Pi p t) _] -> [THPi (Pi p $ addArrowArgs args t)]
  [THBi i t] -> [THBi i $ addArrowArgs args t]
  x -> [THArrow args x]

isArrowTy = \case
  [THArrow{}] -> True
  [THPi (Pi p t)] -> isArrowTy t
  [THBi i t] -> isArrowTy t
  [THSi (Pi p t) _] -> isArrowTy t
  x -> False

getRetTy = \case
  [THArrow _ r] -> getRetTy r -- currying
  [THPi (Pi ps t)] -> getRetTy t
  [THBi i t] -> getRetTy t
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

tyExpr = \case -- expr found as type, (note. raw exprs cannot be types however)
  Ty t -> t
  expr -> error $ "expected type, got: " ++ show expr

tyOfExpr  = \case
  Core x ty -> ty
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
  [THSi (Pi b ty) x] -> getTypeIndexes ty
  [THBi i ty] -> getTypeIndexes ty
  x -> []

--zipWithPad :: a -> b -> (a->b->c) -> [a] -> [b] -> [c]
--zipWithPad a b f = go where
--  go [] y = zipWith f (repeat a) y
--  go x [] = zipWith f x (repeat b)
--  go (x:xs) (y:ys) = f x y : go xs ys

mergeIndex :: Expr -> Expr -> Expr
mergeIndex = _

bind2Expr = \case { BindOK e -> e }

------------------------
-- Type Manipulations --
------------------------
eqTyHead a b = kindOf a == kindOf b
kindOf = \case
  THPrim{}  -> KPrim
  THVar{}   -> KVar
  THArrow{} -> KArrow
  _ -> KAny


mergeTypes :: [TyHead] -> [TyHead] -> [TyHead]
mergeTypes l1 l2 = foldr doSub l2 l1

-- add head constructors, transitions and flow edges
doSub :: TyHead -> [TyHead] -> [TyHead]
doSub newTy [] = [newTy]
doSub newTy (ty:tys) = if eqTyHead newTy ty
  then mergeTyHead newTy ty ++ tys
  else (ty : doSub newTy tys)

mergeTyHead :: TyHead -> TyHead -> [TyHead]
mergeTyHead t1 t2 = -- trace (show t1 ++ " ~~ " ++ show t2) $
  let join = [t1 , t2]
      zM = zipWith mergeTypes
  in case join of
  [THSet a , THSet b] -> [THSet $ max a b]
  [THPrim a , THPrim b]  -> if a == b then [t1] else join
  [THBound a , THBound b]-> if a == b then [t1] else join
  [THVar a , THVar b]    -> if a == b then [t1] else join
  [THArg a , THArg b]    -> if a == b then [t1] else join
  [THRec a , THRec b]    -> if a == b then [t1] else join
  [THExt a , THExt  b]   -> if a == b then [t1] else join
--  [THAlias a , THAlias b] -> if a == b then [t1] else join
  [THSum a , THSum b]     -> [THSum   $ union a b] --[THSum (M.unionWith mergeTypes a b)]
  [THSplit a , THSplit b] -> [THSplit $ union a b] --[THSum (M.unionWith mergeTypes a b)]
--[THProd a , THProd b]   -> [THProd $ intersect a b] -- [THProd (M.unionWith mergeTypes a b)]
  [THProduct a , THProduct b]   -> [THProduct $ IM.intersectionWith mergeTypes a b] -- [THProd (M.unionWith mergeTypes a b)]
  [THArrow d1 r1 , THArrow d2 r2]
    | length d1 == length d2 -> [THArrow (zM d1 d2) (mergeTypes r1 r2)]
  [THFam f1 a1 i1 , THFam f2 a2 i2] -> [THFam (mergeTypes f1 f2) (zM a1 a2) i1] -- TODO merge i1 i2!
  [THPi (Pi b1 t1) , THPi (Pi b2 t2)] -> [THPi $ Pi (b1 ++ b2) (mergeTypes t1 t2)]
  [THPi (Pi b1 t1) , t2] -> [THPi $ Pi b1 (mergeTypes t1 [t2])]
  [t1 , THPi (Pi b1 t2)] -> [THPi $ Pi b1 (mergeTypes [t1] t2)]
--[THRecSi r1 a1 , THRecSi r2 a2] -> if r1 == r2
--  then [THRecSi r1 (zipWith mergeTypes a1 a2)]
--  else join
  _ -> join
