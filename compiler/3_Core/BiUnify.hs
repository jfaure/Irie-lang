-- See presentation/TypeTheory for commentary
module BiUnify (bisub , instantiate) where
import Prim
import CoreSyn as C
import Errors
import CoreUtils
import TCState
import PrettyCore
import Externs
import qualified Data.Vector as V
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

-- useless inferred type: a & (a -> i1 -> i1) -> i1
-- a & a -> i1 -> i1 => (Π B → B → B)

failBiSub :: BiFail -> Type -> Type -> TCEnv s BiCast
failBiSub msg a b = BiEQ <$ (tmpFails %= (TmpBiSubError msg a b:))

bisub a b = (seenVars .= 0) *> do
--when global_debug $ traceM ("bisub: " <> prettyTyRaw a <> " <==> " <> prettyTyRaw b)
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

-- Instantiation; substitute quantified variables with fresh type vars;
-- Note. weird special case (A & {f : B}) typevars as produced by lens over
--   The A serves to propagate the input record, minus the lens field
--   what is meant is really set difference: A =: A // { f : B }
instantiate nb x = freshBiSubs nb >>= \tvars@(tvStart:_) -> doInstantiate tvStart x
-- Replace THBound with fresh TVars
doInstantiate :: Int -> [TyHead] -> TCEnv s [TyHead]
doInstantiate tvarStart ty = let
  mapFn hasProduct = let
    r = doInstantiate tvarStart
    in \case
    THBound i -> pure (THVar (tvarStart + i))
    THMu m t  -> THMu m <$> r t
    THTyCon t -> THTyCon <$> case t of
      THArrow as ret -> THArrow   <$> (r `mapM` as) <*> (r ret)
      THProduct as   -> THProduct <$> (r `mapM` as)
      THTuple as     -> THTuple   <$> (r `mapM` as)
      THSumTy as     -> THSumTy   <$> (r `mapM` as)
    t -> pure t
  hasProduct = any (\case { THTyCon THProduct{} -> True ; _ -> False }) ty
  in mapFn hasProduct `mapM` ty

atomicBiSub :: TyHead -> TyHead -> TCEnv s BiCast
atomicBiSub p m = when global_debug (traceM ("⚛bisub: " <> prettyTyRaw [p] <> " <==> " <> prettyTyRaw [m])) *>
 case (p , m) of
  (_ , THTop) -> pure (CastInstr MkTop)
  (THBot , _) -> pure (CastInstr MkBot)
  (THPrim p1 , THPrim p2) -> primBiSub p1 p2
  (THExt a , THExt b) | a == b -> pure BiEQ
  (p , THExt i) -> biSub [p]     =<< fromJust . tyExpr . (`readPrimExtern` i) <$> use externs
  (THExt i , m) -> (`biSub` [m]) =<< fromJust . tyExpr . (`readPrimExtern` i) <$> use externs

  -- Bound vars (removed at +THBi, so should never be encountered during biunification)
  (THBound i , x) -> error $ "unexpected THBound: " <> show i
  (x , THBound i) -> error $ "unexpected THBound: " <> show i
  (x , THBi nb y) -> error $ "unexpected THBi: "    <> show (p,m)

  (THBi nb x , y) -> do
    instantiated <- instantiate nb x
    biSub instantiated [y]

  (THTyCon t1 , THTyCon t2) -> do
    sv <- seenVars <<.= 0
    r <- biSubTyCon p m (t1 , t2)
    seenVars .= sv
    pure r

  (THPi (Pi p ty) , y) -> biSub ty [y]
  (x , THPi (Pi p ty)) -> biSub [x] ty

  (THRecSi f1 a1, THRecSi f2 a2) -> if f1 == f2
    then if (length a1 == length a2) && all identity (zipWith termEq a1 a2)
      then pure BiEQ
      else error $ "RecSi arities mismatch"
    else error $ "RecSi functions do not match ! " ++ show f1 ++ " /= " ++ show f2
  (THSet u , x) -> pure BiEQ
  (x , THSet u) -> pure BiEQ

  (THVars p , m) -> biSub (THVar <$> bitSet2IntList p) [m]
  (p , THVars m) -> biSub [p] (THVar <$> bitSet2IntList m)

  (THVar p , THVar m) -> use bis >>= \v -> BiEQ <$ do
    MV.modify v (\(BiSub a b) -> BiSub (THVar p : a) b) m
    MV.read v m >>= \(BiSub p' m') -> biSub [THVar p] m' --  MV.modify v (\(BiSub a b) -> BiSub a (THVar m : b)) p
    e <- use escapedVars
    when (testBit e m) (escapedVars %= (`setBit` p))
    when (testBit e p) (escapedVars %= (`setBit` m))

  (THVar p , m) -> use seenVars >>= \s -> if (testBit s p) then pure BiEQ else do
    escapees <- use escapedVars
--  m <- extrudeTH escapees mRaw
    use bis >>= \v -> MV.read v p >>= \(BiSub p' m') -> do
    MV.modify v (\(BiSub a b) -> BiSub a (mergeTyHeadType m b)) p
--  MV.modify v (\(BiSub a b) -> BiSub a (mergeTypes m b)) p
    when (testBit escapees p) (escapedVars %= (.|. getTVarsTyHead m))
    -- TODO spawn new tvars in m for m higher level than p (anything not escaped)
    p' `forM_` \case { THVar i -> seenVars %= (`setBit` i) ; _ -> pure () }
    biSub p' [m]
    pure BiEQ

  (p , THVar m) -> use seenVars >>= \s -> if (testBit s m) then pure BiEQ else do
    escapees <- use escapedVars
--  p <- extrudeTH escapees pRaw
    use bis >>= \v -> MV.read v m >>= \(BiSub p' m') -> do
    MV.modify v (\(BiSub a b) -> BiSub (mergeTyHeadType p a) b) m
--  MV.modify v (\(BiSub a b) -> BiSub (mergeTypes p a) b) m
    when (testBit escapees m) (escapedVars %= (.|. getTVarsTyHead p))
    m' `forM_` \case { THVar i -> seenVars %= (`setBit` i) ; _ -> pure () }
    biSub [p] m'
    pure BiEQ

  (x , THTyCon THArrow{}) -> failBiSub (TextMsg "Excess arguments")       [p] [m]
  (THTyCon THArrow{} , x) -> failBiSub (TextMsg "Insufficient arguments") [p] [m]
  (a , b) -> failBiSub (TextMsg "Incompatible types") [a] [b]

-- extrude :: BitSet -> Type -> TCEnv s Type
-- extrude escapees t = concat <$> mapM (extrudeTH escapees) t
-- 
-- extrudeTH :: BitSet -> TyHead -> TCEnv s Type
-- extrudeTH escapees = let e = extrude escapees in \case
--   THVar   v -> (\x -> [x]) <$> (if escapees `testBit` v then pure (THVar v) else (freshBiSubs 1 <&> \[i] -> THVar i))
--   THVars vs -> fmap concat $ (extrudeTH escapees . THVar) `mapM` bitSet2IntList vs
--   THTyCon t -> (\x -> [THTyCon x]) <$> case t of
--     THArrow ars r -> THArrow   <$> (traverse e ars) <*> e r
--     THProduct   r -> THProduct <$> (traverse e r)
--     THSumTy     r -> THSumTy   <$> (traverse e r)
--     THTuple     r -> THTuple   <$> (traverse e r)
--   x -> case x of
--     THExt{}  -> pure [x]
--     THPrim{} -> pure [x]
--     THBot{} -> pure [x]
--     THTop{} -> pure [x]
--     x -> error $ show x
-- --x -> x

-- TODO cache THTycon contained vars?
getTVarsType = foldr (.|.) 0 . map getTVarsTyHead
getTVarsTyHead :: TyHead -> BitSet
getTVarsTyHead = \case
  THVar   v -> setBit 0 v
  THVars vs -> vs
  THTyCon t -> case t of
    THArrow ars r -> foldr (.|.) 0 (getTVarsType r : (getTVarsType <$> ars) )
    THProduct   r -> foldr (.|.) 0 (getTVarsType <$> IM.elems r)
    THSumTy     r -> foldr (.|.) 0 (getTVarsType <$> IM.elems r)
    THTuple     r -> foldr (.|.) 0 (getTVarsType <$> r)
  x -> 0

-- used for computing both differences between 2 IntMaps (alignWith doesn't give access to the ROnly map key)
data KeySubtype
  = LOnly Type         -- OK by record | sumtype subtyping
  | ROnly IName {-IField-} Type  -- KO field not present
  | Both  Type Type    -- biunify the leaf types

-- This is complicated slightly by needing to recover the necessary subtyping casts
biSubTyCon p m = \case
  (THArrow args1 ret1 , THArrow args2 ret2) -> arrowBiSub (args1,args2) (ret1,ret2)
  (THArrow ars ret ,  THSumTy x) -> pure BiEQ --_
  (THTuple x , THTuple y) -> BiEQ <$ V.zipWithM biSub x y
  (THProduct x , THProduct y) -> let --use normFields >>= \nf -> let -- record: fields in the second must all be in the first
    merged     = IM.mergeWithKey (\k a b -> Just (Both a b)) (fmap LOnly) (IM.mapWithKey ROnly) x y
--  normalized = V.fromList $ IM.elems $ IM.mapKeys (nf VU.!) merged
    normalized = V.fromList $ IM.elems merged -- $ IM.mapKeys (nf VU.!) merged
    go leafCasts normIdx ty = case ty of
      LOnly a   {- drop     -} -> pure $ leafCasts --(field : drops , leafCasts)
      ROnly f a {- no subty -} -> leafCasts <$ failBiSub (AbsentField (QName f)) [p] [m]
      Both  a b {- leafcast -} -> biSub a b <&> (\x -> (normIdx , x) : leafCasts) -- leaf bicast
    in V.ifoldM go [] normalized <&> \leafCasts ->
       let drops = V.length normalized - length leafCasts -- TODO rm filthy list length
       in if drops > 0
       then CastProduct drops leafCasts -- dropped some fields
       else let leaves = snd <$> leafCasts
       in if all (\case {BiEQ->True;_->False}) leaves then BiEQ else CastLeaves leaves
  (THSumTy x , THSumTy y) -> let
    go label subType = case y IM.!? label of -- y must contain supertypes of all x labels
      Nothing -> failBiSub (AbsentLabel (QName label)) [p] [m]
      Just superType -> biSub subType superType
    in BiEQ <$ (go `IM.traverseWithKey` x) -- TODO bicasts
  (THSumTy s , THArrow args retT) | [(lName , tuple)] <- IM.toList s -> -- singleton sumtype => Partial application of Label
    let t' = case tuple of
               [THTyCon (THTuple x)] -> [THTyCon $ THTuple (x V.++ V.fromList args)]
               x                     -> [THTyCon $ THTuple (V.fromList (x : args))]
    in biSub [THTyCon (THSumTy $ IM.singleton lName t')] retT
  (THSumTy s , THArrow{}) | [single] <- IM.toList s -> failBiSub (TextMsg "Note. Labels must be fully applied to avoid ambiguity") [p] [m]
  (a , b)         -> failBiSub TyConMismatch [p] [m]

arrowBiSub (argsp,argsm) (retp,retm) = let
  bsArgs [] [] = ([] , Nothing , ) <$> biSub retp retm
  bsArgs x  [] = ([] , Just x  , ) <$> biSub (prependArrowArgs x retp) retm  -- Partial application
  bsArgs []  x = ([] , Nothing , ) <$> biSub retp (prependArrowArgs x retm)  -- Returns a function
  bsArgs (p : ps) (m : ms) = (\arg (xs,pap,retbi) -> (arg:xs , pap , retbi)) <$> biSub m p <*> bsArgs ps ms
  in (\(argCasts, pap, retCast) -> CastApp argCasts pap retCast) <$> bsArgs argsp argsm

primBiSub p1 m1 = case (p1 , m1) of
  (PrimInt p , PrimInt m) -> if p == m then pure BiEQ else if m > p then pure (CastInstr Zext) else (BiEQ <$ failBiSub (TextMsg "Primitive Finite Int") [THPrim p1] [THPrim m1])
  (PrimInt p , PrimBigInt) -> pure (CastInstr (GMPZext p))
  (p , m) -> if (p /= m) then (failBiSub (TextMsg "primitive types") [THPrim p1] [THPrim m1]) else pure BiEQ

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
