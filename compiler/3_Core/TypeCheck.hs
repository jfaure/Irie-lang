module TypeCheck where
import Prim
import CoreSyn as C
import CoreUtils
import PrettyCore
import Externs
import qualified Data.Vector as V

--------------
-- Checking --
--------------
-- biunification solves constraints `t+ <= t-` ,
-- checking has the form `t- <= t+` (the inferred type must subsume the annotation)
-- we have `t1<=t2 and t1<=t3 ==> t1 <= t2ut3`
-- additionally, subsumption <===> equivalence of typing schemes
-- ie. to decide [d1]t1 <= [d2]t2,
--   * check alpha-equivalence of [d1 n d2]t1 u t2 with [d2]t2
check :: Externs -> V.Vector [TyHead] -> V.Vector (Maybe Type)
     -> [TyHead] -> [TyHead] -> Bool
check e ars labTys inferred gotRaw = let
  go = check' e ars labTys inferred gotRaw
  in if False {-debug getGlobalFlags-}
  then trace ("check: " <> prettyTyRaw inferred <> "\n   <?: " <> prettyTyRaw gotRaw)
    $ go
  else go

--check' :: Externs -> V.Vector [TyHead]
--       -> [TyHead] -> [TyHead] -> Bool
check' es ars labTys inferred gotTy = let
  check'' = check' es ars labTys :: [TyHead] -> [TyHead] -> Bool
  readExt es x = case readPrimExtern es x of
    c@Core{} -> error $ "type expected, got: " <> show c
    Ty t -> t
  checkAtomic :: TyHead -> TyHead -> Bool
  checkAtomic inferred gotTy = case (inferred , gotTy) of
    (THSet l1, THSet l2)  -> l1 <= l2
    (THSet 0 , x)         -> True --case x of { THArrow{} -> False ; _ -> True }
    (x , THSet 0)         -> True --case x of { THArrow{} -> False ; _ -> True }
--  (THArg x , gTy)       -> True -- check'' (ars V.! x) [gTy]
    (THVar x , gTy)       -> True -- check'' (bis V.! x) [gTy]
    (lTy , THVar x)       -> False
    (THPrim x , THPrim y) -> x `primSubtypeOf` y
    (THTyCon t1 , THTyCon t2) -> case (t1,t2) of
      (THArrow a1 r1 , THArrow a2 r2) -> let -- handle differing arities (since currying is allowed)
        -- note. (a->(b->c)) is eq to (a->b->c) via currying
        go (x:xs) (y:ys) = check'' y x && go xs ys
        go [] [] = check'' r1 r2
        go [] y  = check'' r1 [THTyCon $ THArrow y r2]
        go x []  = check'' [THTyCon $ THArrow x r1] r2
        in go a1 a2
      (THSumTy labels , t@THArrow{}) -> _
      (THSumTy x , THSumTy y) -> _

--  (t , THPi [] ty tyArgs) -> check'' [t] (tyAp ty tyArgs)
--  (THPi [] ty tyArgs , t) -> check'' (tyAp ty tyArgs) [t]
--  (x , THArg y) -> True -- ?!
--  (THRec x , THRec y) -> x == y
--  (THRec m , x) -> True -- TODO read ty in the bindMap
    (THRecSi f1 a1 , THRecSi f2 a2) -> _
    (THRecSi f1 a1 , THFam{}) -> True -- TODO read from bindMap
    (THFam f ars [] , x) -> checkAtomic (THTyCon $ THArrow ars f) x
    (THFam f [] ixs , THRecSi f1 a1) -> True -- TODO
    (THFam f1 a1 i1 , THFam f2 a2 i2) -> True -- TODO
--  (THFam f1 a1 i1 , x) -> True -- TODO
    (a,b) -> error $ "checking: strange type heads:\n   " <> show a <> "\n   <? " <> show b
  in case inferred of
    []   -> False
    tys  -> all (\t -> any (checkAtomic t) gotTy) tys
