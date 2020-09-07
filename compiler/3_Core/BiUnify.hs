module BiUnify where
import Prim
import qualified ParseSyntax as P
import CoreSyn as C
import CoreUtils
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
-- 2 environments have a greatest lower bound: d1 n d2, where (d1 n d2) (x) = d1(x) n d2(x)
-- interpret d1(x) = T for x not present in d1
-- ! subsumption (on typing schemes) allows instantiation of type variables

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
-- SubConstraints, eg: (t1- -> t1+ <= t2+ -> t2-) = {t2+ <= t1- , t+ <= t2-}

failBiSub a b = error $ "failed bisub:\n    " ++ show a ++ "\n<--> " ++ show b --pure False

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
atomicBiSub p m = -- trace ("⚛bisub: " ++ prettyTy [p] ++ " <==> " ++ prettyTy [m]) $
 case (p , m) of
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

  (THArrow args1 ret1 , THArrow args2 ret2) -> -- TODO arg overflows ?
    zipWithM biSub args2 args1 *> biSub ret1 ret2
  (THPi (Pi p ty) , y) -> biSub ty [y]
  (x , THPi (Pi p ty)) -> biSub [x] ty

  -- record: labels in the first must all be in the second
  (THProd x , THProd y) -> if all (`elem` x) y then pure () else error "Cannot unify recordTypes"
  (THSum  x , THSum y)  -> if all (`elem` y) x then pure () else error "Cannot unify sumtypes"
  (THArrow ars ret, THSplit y) -> pure () -- TODO
----getLabelRetTypes labelIndexes = do
--  labelsV <- use labels
--  let getLabelTy = \case { Just t->t ; Nothing->error "forward reference to label" }
--  labelTys <- MV.read labelsV `mapM` labelIndexes
--  pure $ map (getRetType . getLabelTy) labelTys

  -- TODO subi(mu a.t+ <= t-) = { t+[mu a.t+ / a] <= t- } -- mirror case for t+ <= mu a.t-
  (p , THExt i) -> biSub [p]     =<< tyExpr . (`readExtern` i)<$>use externs
  (THExt i , m) -> (`biSub` [m]) =<< tyExpr . (`readExtern` i)<$>use externs
--  (h@(THSet uni) , (THArrow x ret)) -> biSub [h] ret
  (THRec m , THRec y) -> unless (m == y) $ error "recursive types are not equal"
  (THRec m , x) -> pure () -- TODO ?
  (THRecSi f1 a1, THRecSi f2 a2) -> if f1 == f2
    then if (length a1 == length a2) && all id (zipWith termEq a1 a2)
      then pure ()
      else error $ "RecSi arities mismatch"
    else error $ "RecSi functions do not match ! " ++ show f1 ++ " /= " ++ show f2
  (a , b) -> failBiSub a b

--------------
-- Checking --
--------------
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
  trace ("check: " ++ prettyTy inferred ++ "\n   <?: " ++ prettyTy gotRaw)
  $ check' e ars labTys inferred (reduceType gotRaw)

--check' :: Externs -> V.Vector [TyHead]
--       -> [TyHead] -> [TyHead] -> Bool
check' es ars labTys inferred gotTy = let
  check'' = check' es ars labTys :: [TyHead] -> [TyHead] -> Bool
  readExt es x = case readExtern es x of
    c@Core{} -> error $ "type expected, got: " ++ show c
    Ty t -> t
  checkAtomic :: TyHead -> TyHead -> Bool
  checkAtomic inferred gotTy = case (inferred , gotTy) of
    (THSet l1, THSet l2)  -> l1 <= l2
    (THSet 0 , x)         -> case x of { THArrow{} -> False ; _ -> True }
    (x , THSet 0)         -> case x of { THArrow{} -> False ; _ -> True }
    (THArg x , gTy)       -> True -- check'' (ars V.! x) [gTy]
    (THVar x , gTy)       -> True -- check'' (bis V.! x) [gTy]
    (lTy , THVar x)       -> False
    (THPrim x , THPrim y) -> x `primSubtypeOf` y
    (THArrow a1 r1 , THArrow a2 r2) -> let -- handle differing arities (since currying is allowed)
      -- note. (a->(b->c)) is eq to (a->b->c) via currying
      go (x:xs) (y:ys) = check'' y x && go xs ys
      go [] [] = check'' r1 r2
      go [] y  = check'' r1 [THArrow y r2]
      go x []  = check'' [THArrow x r1] r2
      in go a1 a2
    (THSum labels , t@THArrow{}) -> let -- all alts must subsume the signature
      labelFns = fromJust . (labTys V.!) <$> labels
      in True -- all (`check''` [t]) labelFns
    (THSum x , THSum y)   -> all (`elem` y) x
    (t , THSplit labels) -> let
      getLabelTy = \case { Just t->t ; Nothing->error "forward reference to label" }
      splitTys = (getRetTy . getLabelTy . (labTys V.!)) <$> labels
      in all (check'' [t]) splitTys
    (THProd x , THProd y) -> all (`elem` x) y
--  (t , THPi [] ty tyArgs) -> check'' [t] (tyAp ty tyArgs)
--  (THPi [] ty tyArgs , t) -> check'' (tyAp ty tyArgs) [t]

    (x , THArg y) -> True -- ?!
    (THRec x , THRec y) -> x == y
    (THRec m , x) -> True -- TODO read ty in the bindMap
    (THRecSi f1 a1 , THRecSi f2 a2) -> _
    (THRecSi f1 a1 , THFam{}) -> True -- TODO read from bindMap
    (THFam f ars [] , x) -> checkAtomic (THArrow ars f) x
    (THFam f [] ixs , THRecSi f1 a1) -> True -- TODO
    (THFam f1 a1 i1 , THFam f2 a2 i2) -> True -- TODO
--  (THFam f1 a1 i1 , x) -> True -- TODO
    (a,b) -> error $ "checking: strange type heads:\n   " ++ show a ++ "\n   <? " ++ show b
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
mergeTyHead t1 t2 = -- trace (show t1 ++ " ~~ " ++ show t2) $
  let join = [t1 , t2]
      zM = zipWith mergeTypes
  in case join of
  [THSet a , THSet b] -> [THSet $ max a b]
  [THPrim a , THPrim b]  -> if a == b then [t1] else join
  [THVar a , THVar b]    -> if a == b then [t1] else join
  [THRec a , THRec b]    -> if a == b then [t1] else join
  [THExt a , THExt  b]   -> if a == b then [t1] else join
--  [THAlias a , THAlias b] -> if a == b then [t1] else join
  [THSum a , THSum b]     -> [THSum   $ union a b] --[THSum (M.unionWith mergeTypes a b)]
  [THSplit a , THSplit b] -> [THSplit $ union a b] --[THSum (M.unionWith mergeTypes a b)]
  [THProd a , THProd b]   -> [THProd $ intersect a b] -- [THProd (M.unionWith mergeTypes a b)]
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

-----------------------------
-- Simplification of types --
-----------------------------
-- 1. bring user types into reduced form
-- * unroll mus and merge components, eg.
--   {l1:a} u {l1:b,l2:b} u mg.a->g
--   {l1:aub}ua -> (mg.a->g)
reduceType :: [TyHead] -> [TyHead]
reduceType []  = []
reduceType t = t

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

-- deciding term equalities ..
termEq t1 t2 = case (t1,t2) of
--(Var v1 , Var v2) -> v1 == v2
  x -> True
--x -> False


