-- See presentation/TypeTheory for commentary
module BiUnify where
import Prim
import CoreSyn as C
import CoreUtils
import TCState
import PrettyCore
import Externs
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Mutable as MV
import qualified Data.IntMap as IM
import Control.Lens

-- First class polymorphism:
-- \i => if (i i) true then true else true
-- i used as:
-- i : (i1 -> i1) -> (i1 -> i1)
-- i : i1 -> i1
-- => Need to consider i may be polymorphic
-- i : a -> a

-- inferred type:
-- i : a -> ((i1 -> i1) & a)
-- i : (b -> b) -> ((i1 -> i1) & (b -> b))

failBiSub :: Text -> Type -> Type -> TCEnv s BiCast
failBiSub msg a b = BiEQ <$ (tmpFails %= (TmpBiSubError msg a b:))

biSub_ a b = do
  when global_debug $ traceM ("bisub: " <> prettyTyRaw a <> " <==> " <> prettyTyRaw b)
  biSub a b

biSub :: TyPlus -> TyMinus -> TCEnv s BiCast
biSub a b = let
  in case (a , b) of
  -- lattice top and bottom
  ([] ,  _)  -> pure BiEQ
  (_  , [])  -> pure BiEQ
  ([p] , [m])-> atomicBiSub p m
  -- lattice subconstraints
  (p:ps@(p1:p2) , m) -> biSub [p] m *> biSub ps m
  (p , m:ms) -> biSub p [m] *> biSub p ms

-- merge types and attempt to eliminate the THVar
--solveTVar varI (THVar v) [] = if varI == v then [] else [THVar v]
--solveTVar _ newTy [] = [newTy] -- TODO dangerous ?
solveTVar varI newTy (ty:tys) = -- if eqTyHead newTy ty then mergeTyHead newTy ty `mergeTypes` tys else
  ty : solveTVar varI newTy tys

atomicBiSub :: TyHead -> TyHead -> TCEnv s BiCast
atomicBiSub p m = (\go -> if True && global_debug then trace ("⚛bisub: " <> prettyTyRaw [p] <> " <==> " <> prettyTyRaw [m]) go else go) $
 case (p , m) of
  (_ , THTop) -> pure (CastInstr MkTop)
  (THBot , _) -> pure (CastInstr MkBot)
  (THPrim p1 , THPrim p2) -> primBiSub p1 p2
  (THExt a , THExt b) | a == b -> pure BiEQ
  (p , THExt i) -> biSub [p]     =<< tyExpr . (`readPrimExtern` i)<$>use externs
  (THExt i , m) -> (`biSub` [m]) =<< tyExpr . (`readPrimExtern` i)<$>use externs

  -- Bound vars (removed at THBi, so should never be encountered during biunification)
  (THBound i , x) -> error $ "unexpected THBound: " <> show i
  (x , THBound i) -> error $ "unexpected THBound: " <> show i
  (THBi nb x , y) -> do
    -- make new THVars for the debruijn bound vars here
    level %= (\(Dominion (f,x)) -> Dominion (f,x+nb))
--  bisubs <- (`MV.grow` nb) =<< use bis
--  let blen = MV.length bisubs
--      tvars = [blen - nb .. blen - 1] 
    (r , _) <- withBiSubs nb $ \tvars -> do
      bisubs <- use bis
      [tvars..tvars+nb-1] `forM_` \i -> MV.write bisubs i (BiSub [] [] 0 0)
--    bis .= bisubs
--    r <- biSub (substFreshTVars (blen - nb) x) [y]
      r <- biSub (substFreshTVars tvars x) [y]
      pure r
    -- todo is it ok that substitution of debruijns doesn't distinguish between + and - types
--  insts <- tvars `forM` \i -> MV.read bisubs i
--  traceM $ "Instantiate: " <> show tvars <> "----" <> show insts <> "---" <> show r
--  pure . did_ $ BiInst insts r
    pure r

  (THTyCon t1 , THTyCon t2) -> biSubTyCon p m (t1 , t2)
--(THArray t1 , THPrim (PrimArr p1)) -> biSub t1 [THPrim p1]
  (THPi (Pi p ty) , y) -> biSub ty [y]
  (x , THPi (Pi p ty)) -> biSub [x] ty

  -- Recursive types are not deBruijn indexed ! this means we must note the equivalent mu types
  (THMu a x , THMu b y) | a == b -> biSub x y
  (THMuBound x, THMuBound y) -> if x == y then pure BiEQ else error $ "mu types not equal: " <> show x <> " /= " <> show y
  -- TODO subi(mu a.t+ <= t-) = { t+[mu a.t+ / a] <= t- } -- mirror case for t+ <= mu a.t-
  (x , THMuBound y) -> use bis >>= \d -> MV.read d y >>= biSub [x] . _pSub
  (THMuBound x , y) -> use bis >>= \d -> MV.read d x >>= biSub [y] . _mSub

  (THRecSi f1 a1, THRecSi f2 a2) -> if f1 == f2
    then if (length a1 == length a2) && all identity (zipWith termEq a1 a2)
      then pure BiEQ
      else error $ "RecSi arities mismatch"
    else error $ "RecSi functions do not match ! " ++ show f1 ++ " /= " ++ show f2
  (THSet u , x) -> pure BiEQ
  (x , THSet u) -> pure BiEQ
  (THVar p , THVar m) -> use bis >>= \v -> BiEQ <$ do
    MV.modify v (\(BiSub a b qa qb) -> BiSub (THVar p : a) b qa qb) m
--  MV.modify v (\(BiSub a b qa qb) -> BiSub a (THVar m : b) qa qb) p
    -- We cannot allow vars to point back to each other, otherwise `bisub TVar{} _` will loop
    let isVar v = (\case { THVar x -> x /= v ; _ -> True })
    MV.modify v (\(BiSub a b qa qb) -> if any (isVar p) b then BiSub a b qa qb else BiSub a (THVar m : b) qa qb) p
  (THVar p , m) -> use bis >>= \v -> (_pSub <$> MV.read v p) >>= \t -> do
    MV.modify v (\(BiSub a b qa qb) -> BiSub a (mergeTyHeadType m b) qa qb) p
    biSub t [m]

  (p , THVar m) -> use bis >>= \v -> (_mSub <$> MV.read v m) >>= \t    -> do
    MV.modify v (\(BiSub a b qa qb) -> BiSub (mergeTyHeadType p a) b qa qb) m
    biSub [p] t

  (x , THTyCon THArrow{}) -> failBiSub "Too many arguments"        [p] [m]
  (THTyCon THArrow{} , x) -> failBiSub "Not enough arguments"      [p] [m]
  (a , b) -> failBiSub "" [a] [b]

-- used for computing both differences between 2 IntMaps (sadly alignWith won't give us the ROnly map key)
data KeySubtype
  = LOnly Type         -- OK by record | sumtype subtyping
  | ROnly IField Type  -- KO field not present
  | Both  Type Type    -- biunify the leaf types

biSubTyCon p m = \case
  (THArrow args1 ret1 , THArrow args2 ret2) -> arrowBiSub (args1,args2) (ret1,ret2)
  (THArrow ars ret ,  THSumTy x) -> pure BiEQ --_
  (THTuple x , THTuple y) -> BiEQ <$ V.zipWithM biSub x y
  (THProduct x , THProduct y) -> use normFields >>= \nf -> let -- record: fields in the second must all be in the first
    merged     = IM.mergeWithKey (\k a b -> Just (Both a b)) (fmap LOnly) (IM.mapWithKey ROnly) x y
    normalized = V.fromList $ IM.elems $ IM.mapKeys (nf VU.!) merged
    go leafCasts normIdx ty = case ty of
      LOnly a   {- drop     -} -> pure $ leafCasts --(field : drops , leafCasts)
      ROnly f a {- no subty -} -> leafCasts <$ failBiSub ("Record: absent field: "<>show f) [p] [m]
      Both  a b {- leafcast -} -> biSub a b <&> (\x -> (normIdx , x) : leafCasts) -- leaf bicast
    in V.ifoldM go [] normalized <&> \leafCasts ->
       let drops = V.length normalized - length leafCasts -- TODO rm filthy list length
       in if drops > 0
       then CastProduct drops leafCasts -- dropped some fields
       else let leaves = snd <$> leafCasts
       in if all (\case {BiEQ->True;_->False}) leaves then BiEQ else CastLeaves leaves
  (THSumTy x , THSumTy y) -> let
    go label subType = case y IM.!? label of -- y must contain supertypes of all x labels
      Nothing -> failBiSub ("Sum type: label not present: " <> show label) [p] [m]
      Just superType -> biSub superType subType
    in BiEQ <$ (go `IM.traverseWithKey` x) -- TODO bicasts
  (THSumTy s , THArrow args retT) | [(lName , tuple)] <- IM.toList s -> -- singleton sumtype => Partial application of Label
    let t' = case tuple of
               [THTyCon (THTuple x)] -> [THTyCon $ THTuple (x V.++ V.fromList args)]
               x                     -> [THTyCon $ THTuple (V.fromList (x : args))]
    in biSub [THTyCon (THSumTy $ IM.singleton lName t')] retT
  (THSumTy s , THArrow{}) | [single] <- IM.toList s -> failBiSub "Labels must be fully applied"  [p] [m]
  (a , b)         -> failBiSub "Type constructors mismatch" [p] [m]

arrowBiSub (argsp,argsm) (retp,retm) = let
  bsArgs [] [] = ([] , Nothing , ) <$> biSub retp retm
  bsArgs x  [] = ([] , Just x  , ) <$> biSub (prependArrowArgs x retp) retm  -- Partial application
  bsArgs []  x = ([] , Nothing , ) <$> biSub retp (prependArrowArgs x retm)  -- Returns a function
  bsArgs (p : ps) (m : ms) = (\arg (xs,pap,retbi) -> (arg:xs , pap , retbi)) <$> biSub m p <*> bsArgs ps ms
  in (\(argCasts, pap, retCast) -> CastApp argCasts pap retCast) <$> bsArgs argsp argsm

primBiSub p1 m1 = case (p1 , m1) of
  (PrimInt p , PrimInt m) -> if p == m then pure BiEQ else if m > p then pure (CastInstr Zext) else (BiEQ <$ failBiSub "Primitive Finite Int" [THPrim p1] [THPrim m1])
  (PrimInt p , PrimBigInt) -> pure (CastInstr (GMPZext p))
  (p , m) -> if (p /= m) then (failBiSub "primitive types" [THPrim p1] [THPrim m1]) else pure BiEQ

-- deciding term equalities ..
termEq t1 t2 = case (t1,t2) of
--(Var v1 , Var v2) -> v1 == v2
  x -> True
--x -> False

-- evaluate type application (from THIxPAp s)
tyAp :: [TyHead] -> IM.IntMap Expr -> [TyHead]
tyAp ty argMap = map go ty where
  go :: TyHead -> TyHead = \case
    THTyCon (THArrow as ret) -> THTyCon $ THArrow (map go <$> as) (go <$> ret)
    x -> x
