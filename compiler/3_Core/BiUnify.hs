module BiUnify where
-- See presentation/TypeTheory for commentary
import Prim
import CoreSyn as C
import CoreUtils
import TCState
import PrettyCore
import Externs

import qualified Data.Vector.Mutable as MV -- mutable vectors
import qualified Data.Vector as V
import qualified Data.IntMap as IM
import Control.Lens

failBiSub msg a b = error $ "failed bisub:\n    " ++ show a ++ "\n<--> " ++ show b ++ "\n" ++ msg --pure False

biSub_ a b = if False -- debug getGlobalFlags
  then trace ("bisub: " ++ prettyTyRaw a ++ " <==> " ++ prettyTyRaw b) biSub a b -- *> (dv_ =<< use bis)
  else biSub a b

biSub :: TyPlus -> TyMinus -> TCEnv s BiCast
biSub a b = let
  in case (a , b) of
  -- lattice top and bottom
  ([] ,  _) -> pure BiEQ
  (_  , []) -> pure BiEQ
  -- lattice subconstraints
  ((p1:p2:p3) , m) -> biSub [p1] m *> biSub (p2:p3) m
  (p , (m1:m2:m3)) -> biSub p [m1] *> biSub p (m2:m3)
  ([p] , [m])      -> atomicBiSub p m

-- merge types and attempt to eliminate the THVar
--solveTVar varI (THVar v) [] = if varI == v then [] else [THVar v]
solveTVar _ newTy [] = [newTy] -- TODO dangerous ?
solveTVar varI newTy (ty:tys) = if eqTyHead newTy ty
  then mergeTyHead newTy ty `mergeTypes` tys
  else ty : solveTVar varI newTy tys

atomicBiSub :: TyHead -> TyHead -> TCEnv s BiCast
atomicBiSub p m = (\go -> if True {-debug getGlobalFlags-} then trace ("⚛bisub: " ++ prettyTyRaw [p] ++ " <==> " ++ prettyTyRaw [m]) go else go) $
 case (p , m) of
  -- Bound vars (removed at THBi, so should never be encountered during biunification)
  (THBound i , x) -> error $ "unexpected THBound: " <> show i
  (x , THBound i) -> error $ "unexpected THBound: " <> show i
  (THBi nb x , y) -> do
    -- make new THVars for the debruijn bound vars here
    level %= (\(Dominion (f,x)) -> Dominion (f,x+nb))
    bisubs <- (`MV.grow` nb) =<< use bis
    let blen = MV.length bisubs
        tvars = [blen - nb .. blen - 1] 
    tvars `forM_` \i -> MV.write bisubs i (let tv = [THVar i] in BiSub tv tv)
    bis .= bisubs
    r <- biSub (substFreshTVars (blen - nb) x) [y]
    -- todo substitution of debruijns doesn't distinguish between + and - types

    -- stacks of pi binder ? (the algorithm lifts all pi binds)
    -- simplify ∀0 -> ∀2 ?
--  insts <- tvars `forM` \i -> MV.read bisubs i
--  traceM $ "Instantiate: " <> show tvars <> "----" <> show insts <> "---" <> show r
--  pure . did_ $ BiInst insts r
    pure r

  -- TVars and ArgVars --
  -- merge types and attempt to eliminate the THVar
  -- Lambda-bound in - position can be guessed
  -- Lambda-bound in + position cannot, however we can take note of it's rank-polymorphism
  (THVar p , THVar m) -> use bis >>= \v-> do
    MV.modify v (over pSub (THVar p : )) m $> BiEQ
    MV.modify v (over mSub (THVar m : )) p $> BiEQ
  (THArg p , THVar m) -> do
    use bis >>= \v-> MV.modify v (over pSub (THVar p : )) m $> BiEQ
    use domain >>= \v->MV.modify v (over mSub (foldr (solveTVar p) [THVar m])) p $> BiEQ
  (THVar p , m) -> use bis >>= \v-> MV.modify v (over mSub (m :)) p $> BiEQ

  (p , THVar m) -> use bis >>= \v-> MV.modify v (over pSub (p :)) m $> BiEQ
  (THArg i , m) -> use domain >>= \v->MV.modify v (over mSub (foldr (solveTVar i) [m])) i $> BiEQ
  -- TODO should we ignore + on lambda ? -- pure BiEq
  (p , THArg i) -> use domain >>= \v->MV.modify v (over pSub (foldr (solveTVar i) [p])) i $> BiEQ

  (THSet u , x) -> pure BiEQ
  (x , THSet u) -> pure BiEQ
  (THRec m , x) -> use wip >>= \w -> do
    Guard ms ars <- MV.read w m
    case ars of
      [] -> pure BiEQ
      ars -> biSub (addArrowArgs ((\x->[THArg x]) <$> ars) [THRec m]) [x] -- -> Checking m y doGen (x:ty)) m *> pure BiEQ

  (THPrim p1 , THPrim p2) -> primBiSub p1 p2

  (THArray t1 , THPrim (PrimArr p1)) -> biSub t1 [THPrim p1]

  (THArrow args1 ret1 , THArrow args2 ret2) -> arrowBiSub (args1,args2) (ret1,ret2)

  (THPi (Pi p ty) , y) -> biSub ty [y]
  (x , THPi (Pi p ty)) -> biSub [x] ty

  -- record: fields in the second must all be in the first
  (THProduct x , THProduct y) -> let
    go k ty = case x IM.!? k of
      Nothing -> failBiSub ("field: '" <> show k <> "' not found.") p m
      Just t2 -> biSub t2 ty
    in BiEQ <$ (go `IM.traverseWithKey` y) -- TODO bicasts

--(THProd x , THProd y) -> if all (`elem` x) y then pure BiEQ else error "Cannot unify recordTypes"
  (THSum  x , THSum y)  -> if all (`elem` y) x then pure BiEQ else error "Cannot unify sumtypes"
  (THArrow ars ret, THSplit y) -> pure BiEQ -- labelBiSub-- TODO
  (THArrow ars ret, THTuple y) -> pure BiEQ -- labelBiSub-- TODO
  (THTuple y, THArrow ars ret) -> pure BiEQ -- labelBiSub-- TODO
----getLabelRetTypes labelIndexes = do
--  labelsV <- use labels
--  let getLabelTy = \case { Just t->t ; BiEQ->error "forward reference to label" }
--  labelTys <- MV.read labelsV `mapM` labelIndexes
--  pure $ map (getRetType . getLabelTy) labelTys

  -- TODO subi(mu a.t+ <= t-) = { t+[mu a.t+ / a] <= t- } -- mirror case for t+ <= mu a.t-
  (THExt a , THExt b) | a == b -> pure BiEQ
  (p , THExt i) -> biSub [p]     =<< tyExpr . (`readPrimExtern` i)<$>use externs
  (THExt i , m) -> (`biSub` [m]) =<< tyExpr . (`readPrimExtern` i)<$>use externs
--  (h@(THSet uni) , (THArrow x ret)) -> biSub [h] ret

  -- TODO sort out typevars
--(THRec m , THRec y) -> if (m == y) then pure BiEQ else error "recursive types are not equal"
--(THArrow{} , THRec{}) -> pure BiEQ -- TODO
--(THRec m , THRec y) -> pure BiEQ -- if (m == y) then pure BiEQ else error "recursive types are not equal"
  (THRecSi f1 a1, THRecSi f2 a2) -> if f1 == f2
    then if (length a1 == length a2) && all identity (zipWith termEq a1 a2)
      then pure BiEQ
      else error $ "RecSi arities mismatch"
    else error $ "RecSi functions do not match ! " ++ show f1 ++ " /= " ++ show f2
  (a , b) -> failBiSub "no relation" a b

arrowBiSub (argsp,argsm) (retp,retm) = let -- zipWithM biSub args2 args1 *> biSub ret1 ret2
 -- Note. App return is never cast (?!)
  bsArgs [] [] = pure ([] , Nothing) <* biSub retp retm
  bsArgs x  [] = pure ([] , Just x)  <* biSub (addArrowArgs x retp) retm  -- OK Partial application
  bsArgs []  x = pure ([] , Nothing) <* biSub retp (addArrowArgs x retm)  -- OK if returns a function
--bsArgs (p : ps) (m : ms) = (:) <$> biSub m p <*> bsArgs ps ms
  bsArgs (p : ps) (m : ms) = (\arg (xs,pap) -> (arg:xs , pap)) <$> biSub m p <*> bsArgs ps ms
  in uncurry CastApp <$> bsArgs argsp argsm -- <* biSub retp retm

primBiSub p1 m1 = case (p1 , m1) of
  (PrimInt p , PrimInt m) -> if p == m then pure BiEQ else if m > p then pure (BiCast (Instr Zext)) else (failBiSub "primint no subtype" p1 m1)
  (p , m) -> if (p /= m) then (failBiSub "primtypes no bisub" p1 m1) else pure BiEQ

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
check e ars labTys inferred gotRaw = let
  go = check' e ars labTys inferred (reduceType gotRaw)
  in if False {-debug getGlobalFlags-}
  then trace ("check: " ++ prettyTyRaw inferred ++ "\n   <?: " ++ prettyTyRaw gotRaw)
    $ go
  else go

--check' :: Externs -> V.Vector [TyHead]
--       -> [TyHead] -> [TyHead] -> Bool
check' es ars labTys inferred gotTy = let
  check'' = check' es ars labTys :: [TyHead] -> [TyHead] -> Bool
  readExt es x = case readPrimExtern es x of
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
--  (THProd x , THProd y) -> all (`elem` x) y
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

-- deciding term equalities ..
termEq t1 t2 = case (t1,t2) of
--(Var v1 , Var v2) -> v1 == v2
  x -> True
--x -> False

-- evaluate type application (from THIxPAp s)
tyAp :: [TyHead] -> IM.IntMap Expr -> [TyHead]
tyAp ty argMap = map go ty where
  go :: TyHead -> TyHead = \case
    THArg y -> case IM.lookup y argMap of
      Nothing -> THArg y
      Just (Ty [t]) -> t
    THArrow as ret -> THArrow (map go <$> as) (go <$> ret)
    x -> x
