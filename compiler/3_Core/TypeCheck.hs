module TypeCheck where
import Prim
import CoreSyn as C
--import CoreUtils
import PrettyCore
import Externs
import qualified Data.Vector as V

--------------
-- Checking --
--------------
-- biunification solves constraints `t+ <= t-` ,
-- checking has the form `t- <= t+` (the inferred type must subsume the annotation)
--
-- given f : t, we require that f by polymorphic in a;
-- we are not searching for a particular a, but making a statement true for all a
-- need reduced form (unroll recursive types and merge records)
-- {l:a} & {l:b , x:b} & mu g. a -> g => {l : a & b} & a -> (mu g. a -> g)
--
-- we have `t1<=t2 and t1<=t3 ==> t1 <= t2ut3`
-- additionally, subsumption <===> equivalence of typing schemes
-- ie. to decide [d1]t1 <= [d2]t2,
--   * check alpha-equivalence of [d1 n d2]t1 u t2 with [d2]t2
check :: Externs -> V.Vector Type -> V.Vector (Maybe Type)
     -> Type -> Type -> Bool
check e ars labTys inferred gotRaw = let
  go = check' e ars labTys inferred gotRaw
  in if global_debug -- True {-debug getGlobalFlags-}
  then trace ("check: " <> prettyTyRaw inferred <> "\n   <?: " <> prettyTyRaw gotRaw) go else go

--check' :: Externs -> V.Vector [TyHead]
--       -> [TyHead] -> [TyHead] -> Bool
check' es ars labTys (TyGround inferred) (TyGround gotTy) = let
  check'' = check' es ars labTys :: Type -> Type -> Bool
  readExt x = case readPrimExtern es x of
    c@Core{} -> error $ "type expected, got: " <> show c
    Ty t -> t
  checkAtomic :: TyHead -> TyHead -> Bool
  checkAtomic inferred gotTy = case {-trace (prettyTyRaw [inferred] <> " <?: " <> prettyTyRaw [gotTy])-} (inferred , gotTy) of
    (THExt i , t) -> check'' (readExt i) (TyGround [t])
    (t , THExt i) -> check'' (TyGround [t]) (readExt i)
    (THBound x , THBound y) -> x == y
    (THSet l1, THSet l2)  -> l1 <= l2
    (THSet 0 , x)         -> True --case x of { THArrow{} -> False ; _ -> True }
    (x , THSet 0)         -> True --case x of { THArrow{} -> False ; _ -> True }
--  (THVar x , gTy)       -> True -- check'' (bis V.! x) [gTy]
--  (lTy , THVar x)       -> False
    (THPrim x , THPrim y) -> x `primSubtypeOf` y
    (THMu x _ , THMuBound y) -> y == x
    (THTyCon t1 , THTyCon t2) -> case (t1,t2) of
      (THArrow a1 r1 , THArrow a2 r2) -> let -- handle differing arities (since currying is allowed)
        -- note. (a->(b->c)) is eq to (a->b->c) via currying
        go (x:xs) (y:ys) = check'' y x && go xs ys
        go [] [] = check'' r1 r2
        go [] y  = check'' r1 (TyGround [THTyCon $ THArrow y r2])
        go x []  = check'' (TyGround [THTyCon $ THArrow x r1]) r2
        in go a1 a2
      (THSumTy labels , t@THArrow{}) -> False
      (THSumTy x , THSumTy y)     -> all identity (alignWith (these (const False) (const False) check'') x y)
      (THTuple x , THTuple y)     -> all identity (alignWith (these (const False) (const False) check'') x y)
      (THProduct x , THProduct y) -> all identity (alignWith (these (const False) (const False) check'') x y)
      _ -> False

--  (t , THPi [] ty tyArgs) -> check'' [t] (tyAp ty tyArgs)
--  (THPi [] ty tyArgs , t) -> check'' (tyAp ty tyArgs) [t]
    x -> False
  in case inferred of
    []   -> False
    tys  -> all (\t -> any (checkAtomic t) gotTy) $ tys

{-
alignMu :: Int -> TyHead -> TyHead -> TyHead -> Bool
alignMu x target lty muBound = (if global_debug
  then trace (prettyTyRaw [lty] <> " µ=? " <> prettyTyRaw [muBound] <> " (" <> prettyTyRaw [target] <> ")")
  else identity) $ let
  exactAlign :: Semialign f => f [TyHead] -> f [TyHead] -> f Bool
  exactAlign = let
    aligner [a] [b] = alignMu x target a b
    aligner a   b   = trace ("typejoin in mu: " <> prettyTyRaw a <> " µ<? " <> prettyTyRaw b) False
    in alignWith (these (const False) (const False) (aligner))
--alignL     = alignWith (these (const True) (const False) (\[a] [b] -> alignMu x target a b))
  in case (lty , muBound) of
  (THTyCon (THProduct lt) , THTyCon (THProduct rt)) -> all identity $ exactAlign lt rt
  (THTyCon (THSumTy   lt) , THTyCon (THSumTy   rt)) -> all identity $ exactAlign lt rt -- alignL rt lt
  (THTyCon (THTuple   lt) , THTyCon (THTuple   rt)) -> all identity $ exactAlign lt rt
--(THTyCon (THSumTy lt) , THTyCon (THSumTy rt)) -> exactAlign lt rt
  (THPrim l , THPrim r) -> l == r -- must be exactly equal to roll up mus
  (a , b) -> check _ mempty mempty [a] [b]
--_ -> False
-}
