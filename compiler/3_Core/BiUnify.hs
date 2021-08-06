 -- See presentation/TypeTheory for commentary
module BiUnify where
import Prim
import CoreSyn as C
import CoreUtils
import TCState
import PrettyCore
import Externs

import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.IntMap as IM
import qualified Data.Text as T
import Control.Lens

failBiSub :: (Show a , Show b) => Text -> a -> b -> TCEnv s BiCast
failBiSub msg a b = let
  msg =  msg <> "\nnot a subtype:\n" <> show a <> "\n<:\n" <> show b
--in BiEQ <$ (bisubNoSubtype %= (msg:))
  in panic msg
--handleBiSubFailure = (bisubNoSubtype <<%= (const [])) >>= panic . T.concat

biSub_ a b = do
  when global_debug $ traceM ("bisub: " <> prettyTyRaw a <> " <==> " <> prettyTyRaw b)
  biSub a b

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
--solveTVar _ newTy [] = [newTy] -- TODO dangerous ?
solveTVar varI newTy (ty:tys) = if eqTyHead newTy ty
  then mergeTyHead newTy ty `mergeTypes` tys
  else ty : solveTVar varI newTy tys

atomicBiSub :: TyHead -> TyHead -> TCEnv s BiCast
atomicBiSub p m = (\go -> if global_debug then trace ("⚛bisub: " <> prettyTyRaw [p] <> " <==> " <> prettyTyRaw [m]) go else go) $
 case (p , m) of
  (_ , THTop) -> pure BiEQ
  (THBot , _) -> pure BiEQ
  (THPrim p1 , THPrim p2) -> primBiSub p1 p2
--(h@(THSet uni) , (THArrow x ret)) -> biSub [h] ret
  (THExt a , THExt b) | a == b -> pure BiEQ
  (p , THExt i) -> biSub [p]     =<< tyExpr . (`readPrimExtern` i)<$>use externs
  (THExt i , m) -> (`biSub` [m]) =<< tyExpr . (`readPrimExtern` i)<$>use externs

  -- Bound vars (removed at THBi, so should never be encountered during biunification)
  (THBound i , x) -> panic $ "unexpected THBound: " <> show i
  (x , THBound i) -> panic $ "unexpected THBound: " <> show i
  (THBi nb x , y) -> do
    -- make new THVars for the debruijn bound vars here
    level %= (\(Dominion (f,x)) -> Dominion (f,x+nb))
    bisubs <- (`MV.grow` nb) =<< use bis
    let blen = MV.length bisubs
        tvars = [blen - nb .. blen - 1] 
    tvars `forM_` \i -> MV.write bisubs i (BiSub [] [] 0 0)
    bis .= bisubs
    r <- biSub (substFreshTVars (blen - nb) x) [y]
    -- todo is it ok that substitution of debruijns doesn't distinguish between + and - types
--  insts <- tvars `forM` \i -> MV.read bisubs i
--  traceM $ "Instantiate: " <> show tvars <> "----" <> show insts <> "---" <> show r
--  pure . did_ $ BiInst insts r
    pure r

  (THArrow args1 ret1 , THArrow args2 ret2) -> arrowBiSub (args1,args2) (ret1,ret2)
  (THArrow ars ret ,  THSumTy x) -> pure BiEQ --_
  (THPi (Pi p ty) , y) -> biSub ty [y]
  (x , THPi (Pi p ty)) -> biSub [x] ty
  (THTuple x , THTuple y) -> BiEQ <$ V.zipWithM biSub x y
  (THProduct x , THProduct y) -> let -- record: fields in the second must all be in the first
    go k ty = case x IM.!? k of
      Nothing -> failBiSub ("field: '" <> show k <> "' not found.") p m
      Just t2 -> biSub t2 ty
    in BiEQ <$ (go `IM.traverseWithKey` y) -- TODO bicasts
  (THSumTy x , THSumTy y) -> let
    go label subType = case y IM.!? label of -- y must contain supertypes of all x labels
      Nothing -> failBiSub ("Sumtype: label not present: " <> show label) p m
      Just superType -> biSub superType subType
    in BiEQ <$ (go `IM.traverseWithKey` x) -- TODO bicasts
  (THArray t1 , THPrim (PrimArr p1)) -> biSub t1 [THPrim p1]
  (THArrow ars ret, THTuple y) -> pure BiEQ -- labelBiSub-- TODO
  (THTuple y, THArrow ars ret) -> pure BiEQ -- labelBiSub-- TODO

  -- TODO subi(mu a.t+ <= t-) = { t+[mu a.t+ / a] <= t- } -- mirror case for t+ <= mu a.t-
  -- Recursive types are not deBruijn indexed ! this means we must note the equivalent mu types
  (THMu a x , THMu b y) | a == b -> do --(muEqui %= IM.insert a b) *>  do
    biSub x y
--  ret <$ (muEqui %= IM.delete a)
--(x , THMu i y) -> biSub [x] y -- TODO is it alright to drop mus ?
--(THMu i x , y) -> biSub x [y] -- TODO is it alright to drop mus ?
  (THMuBound x, THMuBound y) -> use muEqui >>= \equi -> case (equi IM.!? x) of
    Just found -> if found == y then pure BiEQ else error $ "mu types not equal: " <> show x <> " /= " <> show y
    Nothing -> error $ "panic Mu bound variable without outer binder!" -- TODO can maybe be legit
  -- TODO can unrolling recursive types loop ?
  (x , THMuBound y) -> use bis >>= \d -> MV.read d y >>= biSub [x] . _pSub -- unroll recursive types
  (THMuBound x , y) -> use bis >>= \d -> MV.read d x >>= biSub [y] . _mSub -- unroll recursive types

  (THRecSi f1 a1, THRecSi f2 a2) -> if f1 == f2
    then if (length a1 == length a2) && all identity (zipWith termEq a1 a2)
      then pure BiEQ
      else error $ "RecSi arities mismatch"
    else error $ "RecSi functions do not match ! " ++ show f1 ++ " /= " ++ show f2
  (THSet u , x) -> pure BiEQ
  (x , THSet u) -> pure BiEQ
  (THVar p , THVar m) -> use bis >>= \v -> BiEQ <$ do
    MV.modify v (\(BiSub a b qa qb) -> BiSub (THVar p : a) b qa qb) m
    MV.modify v (\(BiSub a b qa qb) -> BiSub a (THVar m : b) qa qb) p
    dupVar True m
--  dupVar False p
  (THVar p , m) -> use bis >>= \v -> (_pSub <$> MV.read v p) >>= \t -> do
    MV.modify v (\(BiSub a b qa qb) -> BiSub a (m : b) (1+qa) qb) p
    dupp p True [m] -- Not entirely convinced by this , should only affect higher-rank polymorphism
    biSub t [m]
  (p , THVar m) -> use bis >>= \v -> (_mSub <$> MV.read v m) >>= \t    -> do
    MV.modify v (\(BiSub a b qa qb) -> BiSub (p : a) b qa qb) m
--  case m == 53 || m == 38 of -- recursive types shouldn't be dup'd
--    True  -> pure [] --dupp m True [p] -- special case for recursive bisub
--    False -> dupp m False [p]
--  dupp m False [p]
--  when (isTyCon p) (void $ dupp m False [p])
    biSub [p] t

  (a , b) -> failBiSub "no relation" a b

arrowBiSub (argsp,argsm) (retp,retm) = let -- zipWithM biSub args2 args1 *> biSub ret1 ret2
 -- Note. App return is never cast (?!)
  bsArgs [] [] = pure ([] , Nothing) <* biSub retp retm
  bsArgs x  [] = pure ([] , Just x)  <* biSub (addArrowArgs x retp) retm  -- Partial application
  bsArgs []  x = pure ([] , Nothing) <* biSub retp (addArrowArgs x retm)  -- Returns a function
--bsArgs (p : ps) (m : ms) = (:) <$> biSub m p <*> bsArgs ps ms
  bsArgs (p : ps) (m : ms) = (\arg (xs,pap) -> (arg:xs , pap)) <$> biSub m p <*> bsArgs ps ms
  in uncurry CastApp <$> bsArgs argsp argsm -- <* biSub retp retm

primBiSub p1 m1 = case (p1 , m1) of
  (PrimInt p , PrimInt m) -> if p == m then pure BiEQ else if m > p then pure (BiCast (Instr Zext)) else (failBiSub "primint no subtype" p1 m1)
  (p , m) -> if (p /= m) then (failBiSub "primtypes no bisub" p1 m1) else pure BiEQ

-- deciding term equalities ..
termEq t1 t2 = case (t1,t2) of
--(Var v1 , Var v2) -> v1 == v2
  x -> True
--x -> False

-- evaluate type application (from THIxPAp s)
tyAp :: [TyHead] -> IM.IntMap Expr -> [TyHead]
tyAp ty argMap = map go ty where
  go :: TyHead -> TyHead = \case
    THArrow as ret -> THArrow (map go <$> as) (go <$> ret)
    x -> x
