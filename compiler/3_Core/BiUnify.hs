module BiUnify where
import Prim
import qualified ParseSyntax as P
import CoreSyn as C
import TCState
import PrettyCore
import qualified CoreUtils as CU
import DesugarParse
import Externs

import qualified Data.Vector.Mutable as MV -- mutable vectors
import qualified Data.Vector as V
import qualified Data.Map as M
import qualified Data.IntMap as IM
import qualified Data.Text as T
import Data.Functor
import Control.Monad
import Control.Applicative
import Control.Monad.Trans.State.Strict
import Data.List --(foldl', intersect)
import Control.Lens

import Debug.Trace
d_ x   = trace (clYellow (show x))
did_ x = d_ x x

-------------------
-- BiSubstitution --
-------------------
-- BiSubstitution solves constraints of the form t+ <= t-
-- Atomic: (join/meet a type to the var)
-- a  <= t- solved by [m- b = a n [b/a-]t- /a-] 
-- t+ <= a  solved by [m+ b = a u [b/a+]t+ /a+] 
-- a  <= c  solved by [m- b = a n [b/a-]c  /a-] -- (or equivalently,  [a u b /b+])
-- SubConstraints:
-- (t1- -> t1+ <= t2+ -> t2-) = {t2+ <= t1- , t+ <= t2-}
biSub_ a b = trace ("bisub: " ++ show a ++ " <==> " ++ show b) biSub a b
biSub :: TyPlus -> TyMinus -> TCEnv s ()
biSub a b = case (a , b) of
  -- lattice top and bottom
  ([] ,  _) -> pure ()
  (_  , []) -> pure ()
  -- atomic constraints

  -- Lambda-bound in negative position can now be guessed
  (p , [THArg i]) -> use domain >>= \v->MV.modify v (++p) i
  ([THVar p] , m) -> use bis >>= \v->MV.modify v
    (over mSub (foldr (doSub p) m)) p
  (p , [THVar m]) -> use bis >>= \v->MV.modify v
    (over pSub (foldr (doSub m) p)) m

  (p , [THImplicit i]) -> pure ()
  ([THImplicit i] , p) -> pure ()

  ([THPrim p1] , [THPrim p2]) -> when (p1 /= p2) (failBiSub p1 p2)
  ([THArray t1] , [THPrim (PrimArr p1)]) -> biSub t1 [THPrim p1]

  -- lattice subconstraints
  ((p1:p2:p3) , m) -> biSub [p1] m *> biSub (p2:p3) m
  (p , (m1:m2:m3)) -> biSub p [m1] *> biSub p (m2:m3)
  (p , [THExt i])  -> biSub p =<< tyExpr . (V.! i) <$> use externs
  ([THExt i] , m)  -> (`biSub` m) =<< tyExpr . (V.! i) <$> use externs

  -- basic head constructor subconstraints
  ([THArrow args1 ret1] , [THArrow args2 ret2]) -> zipWithM biSub args2 args1 *> biSub ret1 ret2
  -- record: labels in the first must all be in the second
  ([THProd fields1] , [THProd fields2]) -> let
    go (l , ttm) = case M.lookup l fields1 of
      Nothing  -> error $ "label not present"
      Just ttp -> biSub ttp ttm --covariant
    in go `mapM_` (M.toList fields2)

  ([THRec i p] , m) -> _
  (p , [THRec i m]) -> _

  (h@[THHigher uni] , [THArrow x ret]) -> biSub h ret

  -- lattice components without subtyping relation
  (a , b) -> failBiSub a b

failBiSub a b = error $ "failed bisub: " ++ show a ++ "<-->" ++ show b --pure False

--------------
-- Checking --
--------------
-- 1. bring user types into reduced form
-- * unroll mus and merge components, eg.
--   {l1:a} u {l1:b,l2:b} u mg.a->g
--   {l1:aub}ua -> (mg.a->g)
reduceType :: [TyHead] -> [TyHead]
reduceType []  = []
reduceType t = t
--reduceType (t1:tys) = let
--  mergeTy :: [TyHead] -> [TyHead] -> [TyHead]
--  mergeTy ty []     = ty
--  mergeTy ty (tc:tcs) = if eqTyHead tc ty then (ty:tc:tcs) else mergeTy tcs ty
--  mergeTy (THRec i t) tList = t -- TODO unroll
--  in foldr mergeTy t1 tys

-- biunification solves constraints `t+ <= t-` , but checking has the form `t- <= t+`
-- we have t1<=t2 and t1<=t3 ==> t1 <= t2ut3
-- additionally, subsumption <===> equivalence of typing schemes
-- ie. to decide [d1]t1 <= [d2]t2, we check alpha-equivalence of [d1 n d2]t1 u t2 with [d2]t2
check :: [TyHead] -> Set -> TCEnv s a -> Bool
check gotRaw expRaw delta = let
  gotTy = reduceType gotRaw ; expTy = reduceType expRaw
  _check ty = True
  in  all _check gotTy

mkTcFailMsg gotTerm gotTy expTy =
  ("subsumption failure:"
  ++ "\nExpected: " ++ show expTy
  ++ "\nGot:      " ++ show gotTy
-- ++ "\n" ++ show (unVar gotTy) ++ " <:? " ++ show expected
  ++ "\nIn the expression: " ++ show gotTy
  )

eqTyHead a b = kindOf a == kindOf b
kindOf = \case
  THPrim{}  -> KPrim
  THAlias{} -> _ -- have to deref it
  THVar{}   -> KVar
  THArrow{} -> KArrow
  THRec{}   -> _
  _ -> KAny

mergeTypes :: [TyHead] -> [TyHead] -> [TyHead]
mergeTypes l1 l2 = foldr (\a b -> doSub (-1) a b) l2 l1

-- merge a tyhead into a bisub ; remove the typevar if resolved
-- mu binders ?
-- doSub i = (:)
doSub :: Int -> TyHead -> [TyHead] -> [TyHead]
doSub i (THVar v) [] = if i == v then [] else [THVar v]
doSub i newTy [] = [newTy]
doSub i newTy (ty:tys) = if eqTyHead newTy ty
  then mergeTyHead i newTy ty ++ tys
  else (ty : doSub i newTy tys)

mergeTyHead :: Int -> TyHead -> TyHead -> [TyHead]
mergeTyHead int t1 t2 = let join = [t1 , t2] in case join of
  [THPrim a , THPrim b]   -> if a == b then [t1] else join
  [THVar a , THVar b]     -> if a == b then [t1] else join
  [THAlias a , THAlias b] -> if a == b then [t1] else join
  [THSum a , THSum b]   -> _
  [THProd a , THProd b] -> _
--[THArrow a , THArrow b] -> _
  _ -> join
