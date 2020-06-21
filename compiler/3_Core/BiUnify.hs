module BiUnify where
import Prim
import qualified ParseSyntax as P
import CoreSyn as C
import TCState
import PrettyCore
import DesugarParse
import Externs

import qualified Data.Vector.Mutable as MV -- mutable vectors
import qualified Data.Vector as V
import qualified Data.Map as M
import qualified Data.IntMap as IM
import qualified Data.Text as T
import Data.Functor
import Data.Maybe
import Control.Monad
import Control.Applicative
import Control.Monad.Trans.State.Strict
import Data.List --(foldl', intersect)
import Control.Lens
import Debug.Trace

--------------------------------------------
-- Monotype environments (typing schemes) --
--------------------------------------------
-- 2 environments have a greatest lower bound: d1 n d2,
-- where (d1 n d2) (x) = d1(x) n d2(x)
-- interpret d1(x) = T for x not present in d1
-- ! subsumption (on typing schemes)
--   allows instantiation of type variables

--------------------
-- Generalization --
--------------------
-- suppose `e = let x = e1 in e2`. e1 must be typeable and have principal ty [D1-]t1+ under Pi
-- the most general choice is to insert x into Pi with principal type of e1
-- ie. x depends on lambda-bound vars, so those are moved into Pi (as monotype environments)

-------------------------------
-- Note. Rank-n polymorphism --
-------------------------------
-- A constraint a <= t- gives a an upper bound ;
-- which only affects a when used as an upper bound (negative position)
-- The only exception is when inferring higher-rank polymorphism,
-- since a- and a+ must have the same polymorphic rank

-------------------
-- BiSubstitution --
-------------------
-- find substitution solving constraints of the form t+ <= t-
-- Atomic: (join/meet a type to the var)
-- a  <= t- solved by [m- b = a n [b/a-]t- /a-] 
-- t+ <= a  solved by [m+ b = a u [b/a+]t+ /a+] 
-- a  <= c  solved by [m- b = a n [b/a-]c  /a-] -- (or equivalently,  [a u b /b+])
-- SubConstraints:
-- (t1- -> t1+ <= t2+ -> t2-) = {t2+ <= t1- , t+ <= t2-}

failBiSub a b = error $ "failed bisub: " ++ show a ++ "<-->" ++ show b --pure False

biSub_ a b = trace ("bisub: " ++ prettyTy a ++ " <==> " ++ prettyTy b) biSub a b -- *> (dv_ =<< use bis)
biSub :: TyPlus -> TyMinus -> TCEnv s ()
biSub a b = let
  solveTVar varI (THVar v) [] = if varI == v then [] else [THVar v]
  solveTVar _ newTy [] = [newTy]
  solveTVar varI newTy (ty:tys) = if eqTyHead newTy ty
    then mergeTyHead newTy ty ++ tys
    else ty : solveTVar varI newTy tys
  in case (a , b) of
  -- lattice top and bottom
  ([] ,  _) -> pure ()
  (_  , []) -> pure ()
  -- vars
  ([THVar p] , m) -> use bis >>= \v->MV.modify v
    (over mSub (foldr (solveTVar p) m)) p
  (p , [THVar m]) -> use bis >>= \v->MV.modify v
    (over pSub (foldr (solveTVar m) p)) m
  -- lattice subconstraints
  ((p1:p2:p3) , m) -> biSub [p1] m *> biSub (p2:p3) m
  (p , (m1:m2:m3)) -> biSub p [m1] *> biSub p (m2:m3)
  ([p] , [m])      -> atomicBiSub p m

atomicBiSub :: TyHead -> TyHead -> TCEnv s ()
atomicBiSub p m = case (p , m) of
  -- Lambda-bound in - position can be guessed
  (THArg i , m) -> let
    replaceLambda t = \case { [THArg i2] | i2==i -> [t] ; x -> doSub t x }
    in use domain >>= \v->MV.modify v (over mSub (replaceLambda m)) i
  (p , THArg i) -> pure () -- use domain >>= \v->MV.modify v (over pSub (doSub p)) i
---- lambda-bound in + position is ignored except for info on rank-n polymorphism info

--(THArg i , THArrow args ret) -> let
--    fa = [THImplicit i] ; ty = THArrow (replicate (length args) fa) fa
--  in use domain >>= \v-> MV.modify v (ty:) i
  (THSet u , x) -> pure ()
  (THRec m , THSet u) -> pure ()
  (THPrim p1 , THPrim p2) -> when (p1 /= p2) (failBiSub p1 p2)
  (THArray t1 , THPrim (PrimArr p1)) -> biSub t1 [THPrim p1]

  (THArrow args1 ret1 , THArrow args2 ret2) ->
    zipWithM biSub args2 args1 *> biSub ret1 ret2

  -- record: labels in the first must all be in the second
  (THProd x , THProd y) -> if all (`elem` y) x then pure () else error "Cannot unify recordTypes"
  (THSum  x , THSum y)  -> if all (`elem` x) y then pure () else error "Cannot unify sumtypes"

  -- TODO subi(mu a.t+ <= t-) = { t+[mu a.t+ / a] <= t- } -- mirror case for t+ <= mu a.t-
  (p , THExt i) -> biSub [p]     =<< tyExpr . (`readExtern` i)<$>use externs
  (THExt i , m) -> (`biSub` [m]) =<< tyExpr . (`readExtern` i)<$>use externs
--  (h@(THSet uni) , (THArrow x ret)) -> biSub [h] ret
  (THRec m , THRec y) -> unless (m == y) $ error "recursive types are not equal"
  (THRec m , x) -> pure () -- TODO ?
--(THULC a , THULC b) -> biSubULC a b
  (a , b) -> failBiSub a b

biSubULC a b = pure ()
--if a == b then pure () else failBiSub a b
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

-- biunification solves constraints `t+ <= t-` ,
-- checking has the form `t- <= t+`
-- (the inferred type must subsume the annotation)
-- we have `t1<=t2 and t1<=t3 ==> t1 <= t2ut3`
-- additionally, subsumption <===> equivalence of typing schemes
-- ie. to decide [d1]t1 <= [d2]t2,
--   * check alpha-equivalence of [d1 n d2]t1 u t2 with [d2]t2
check :: Externs -> V.Vector [TyHead] -> V.Vector (Maybe Type)
     -> [TyHead] -> [TyHead] -> Bool
check e ars labTys inferred gotRaw =
  trace ("check: " ++ prettyTy inferred ++ "\n<? " ++ prettyTy gotRaw)
  $ check' e ars labTys inferred (reduceType gotRaw)

--check' :: Externs -> V.Vector [TyHead]
--       -> [TyHead] -> [TyHead] -> Bool
check' es ars labTys inferred gotTy = let
  check'' = check' es ars labTys
  readExt es x = case readExtern es x of
    c@Core{} -> error $ "type expected, got: " ++ show c
    Ty t -> t
  checkAtomic :: TyHead -> TyHead -> Bool
  checkAtomic inferred gotTy = case (inferred , gotTy) of
    (THSet l1, THSet l2)  -> l1 <= l2
    (THSet 0 , x)         -> case x of
        THArrow{} -> False
        _         -> True
    (x , THSet 0)         -> case x of
        THArrow{} -> False
        _         -> True
    (THArg x , gTy)       -> True -- check'' (ars V.! x) [gTy]
    (THVar x , gTy)       -> True -- check'' (bis V.! x) [gTy]
    (lTy , THVar x)       -> False
    (THPrim x , THPrim y) -> x `primSubtypeOf` y
    (THArrow a1 r1 , THArrow a2 r2) -> let
      -- note. (a->(b->c)) is eq to (a->b->c) via currying
      mkFn [x] = x
      mkFn s = let (ars , [ret]) = splitAt (length s - 1) s
        in [THArrow ars ret]
      go (x:xs) (y:ys) = check'' y x && go xs ys
      go [] [] = check'' r1 r2
      go [] y  = check'' r1 [THArrow y r2]
      go x []  = check'' [THArrow x r1] r2
      in go a1 a2
    (THSum labels , t@THArrow{}) -> let -- all alts must subsume the signature
--    getConTy = \case
--      [THULC lc] -> let
--        ulcFnApp2Ty = \case
--          LCApp f x
      labelFns = fromJust . (labTys V.!) <$> labels
      in True -- all (`check''` [t]) labelFns
    (THSum x , THSum y)   -> all (`elem` y) x
--    int = M.intersection y x -- left-biased
--    szOK = M.size x <= M.size y
--    in szOK && all id (zipWith check'' (M.elems x) (M.elems int))
    (THProd x , THProd y) -> all (`elem` x) y
--    int = M.intersection y x -- left-biased
--    szOK = M.size x >= M.size y
--    in szOK && all id (zipWith check'' (M.elems x) (M.elems int))
--  (THULC (LCExt x) , THULC (LCExt y)) -> x == y
--  (THULC (LCExt x) , t) -> check'' (readExt es x) [t]
--  (t , THULC (LCExt x)) -> check'' [t] (readExt es x)
--  (t , THIxPAp [] ty tyArgs termArgs) -> check' es (ars V.// M.toList tyArgs) [t] ty
--  (t , THPi [] ty tyArgs) -> check'' [t] (tyAp ty tyArgs)
--  (THPi [] ty tyArgs , t) -> check'' (tyAp ty tyArgs) [t]

    (x , THArg y) -> True -- ?!
    (THRec x , THRec y) -> x == y
    (THRec m , x) -> True -- TODO read ty in the bindMap
    (a,b) -> error $ "checking: not ready for: " ++ show a ++ " <? " ++ show b
  in case inferred of
    []   -> False
    tys  -> all (\t -> any (checkAtomic t) gotTy) tys

mergeTypes :: [TyHead] -> [TyHead] -> [TyHead]
mergeTypes l1 l2 = foldr doSub l2 l1

-- add head constructors, transitions and flow edges
doSub :: TyHead -> [TyHead] -> [TyHead]
doSub newTy [] = [newTy]
doSub newTy (ty:tys) = if eqTyHead newTy ty
  then mergeTyHead newTy ty ++ tys
  else (ty : doSub newTy tys)

mergeTyHead :: TyHead -> TyHead -> [TyHead]
mergeTyHead t1 t2 = let join = [t1 , t2] in case join of
  [THPrim a , THPrim b]   -> if a == b then [t1] else join
  [THVar a , THVar b]     -> if a == b then [t1] else join
--  [THULC a , THULC b]     -> join
--  [THExt  a , THExt  b]   -> if a == b then [t1] else join
--  [THAlias a , THAlias b] -> if a == b then [t1] else join
  [THSum a , THSum b]     -> [THSum  $ intersect a b] --[THSum (M.unionWith mergeTypes a b)]
  [THProd a , THProd b]   -> [THProd $ union a b] -- [THProd (M.unionWith mergeTypes a b)]
--[THArrow a , THArrow b] -> _
--_ -> _
  _ -> join

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
  THVar{}   -> KVar
  THArrow{} -> KArrow
  _ -> KAny
