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

-- inferred type: a & (a -> i1 -> i1) -> i1
-- contravariant recursive type; this only makes sense if a is higher rank polymorphic:
-- a & a -> i1 -> i1 => (Π B → B → B)

failBiSub :: BiFail -> Type -> Type -> TCEnv s BiCast
failBiSub msg a b = BiEQ <$ (tmpFails %= (TmpBiSubError msg a b:))

bisub a b = --when global_debug (traceM ("bisub: " <> prettyTyRaw a <> " <==> " <> prettyTyRaw b)) *>
  biSubType a b

biSubTVars :: BitSet -> BitSet -> TCEnv s BiCast
biSubTVars p m = BiEQ <$ (bitSet2IntList p `forM` \v -> biSubTVarTVar v `mapM` bitSet2IntList m)

biSubTVarTVar p m = use deadVars >>= \dead -> -- if testBit ls p || testBit ls m then pure BiEQ else
  use bis >>= \v -> MV.read v p >>= \(BiSub p' m') -> do
    when global_debug (traceM ("bisub: " <> prettyTyRaw (TyVar p) <> " <==> " <> prettyTyRaw (TyVar m)))
    MV.write v p (BiSub p' (mergeTVar m m'))
    unless (hasVar m' m || testBit dead p) $ void (biSubType p' (TyVar m))
    pure BiEQ

biSubTVarP v m = use deadVars >>= \dead -> -- if testBit ls v then pure BiEQ else
  use bis >>= \b -> MV.read b v >>= \(BiSub p' m') -> do
    let mMerged = mergeTypes False m m'
    when global_debug (traceM ("bisub: " <> prettyTyRaw (TyVar v) <> " <==> " <> prettyTyRaw m))
    use escapedVars >>= \es -> when (testBit es v) $ leakedVars %= (.|. getTVarsType m)
    MV.write b v (BiSub p' mMerged)
    if (mMerged == m' || testBit dead v) then pure BiEQ -- if merging was noop, this would probably loop
    else biSubType p' m

biSubTVarM p v = use deadVars >>= \dead -> -- if testBit ls v then pure BiEQ else
  use bis >>= \b -> MV.read b v >>= \(BiSub p' m') -> do
    let pMerged = mergeTypes True p p'
    when global_debug (traceM ("bisub: " <> prettyTyRaw p <> " <==> " <> prettyTyRaw (TyVar v)))
    use escapedVars >>= \es -> when (testBit es v) $ leakedVars %= (.|. getTVarsType p)
    MV.write b v (BiSub pMerged m')
    if (pMerged == p' || testBit dead v) then pure BiEQ -- if merging was noop, this would probably loop
    else biSubType p m'

biSubType :: Type -> Type -> TCEnv s BiCast
biSubType tyP tyM =
  let ((pVs , pTs) , (mVs , mTs)) = (partitionType tyP , partitionType tyM) in do
    biSubTVars pVs mVs
    unless (null mTs) $ bitSet2IntList pVs `forM_` \v -> biSubTVarP v (TyGround mTs)
    unless (null pTs) $ bitSet2IntList mVs `forM_` \v -> biSubTVarM (TyGround pTs) v
    biSub pTs mTs
    pure BiEQ

-- bisub on ground types
biSub :: [TyHead] -> [TyHead] -> TCEnv s BiCast
biSub a b = case (a , b) of
  ([] ,  _)  -> pure BiEQ
  (_  , [])  -> pure BiEQ
  (p , m)    -> BiEQ <$ (p `forM` \aP -> atomicBiSub aP `mapM` m)

-- Instantiation; substitute quantified variables with fresh type vars;
-- Note. weird special case (A & {f : B}) typevars as produced by lens over
--   The A serves to propagate the input record, minus the lens field
--   what is meant is really set difference: A =: A // { f : B }
instantiate nb x = do
  sv <- muInstances <<.= mempty
  r <- if nb == 0 then doInstantiate mempty x else
    freshBiSubs nb >>= \tvars@(tvStart:_) -> doInstantiate (IM.fromList (zip [0..] tvars)) x
  muInstances .= sv
  pure r

-- Replace THBound with fresh TVars
-- this mixes mu-bound vars xyz.. and generalised vars A..Z
doInstantiate :: IM.IntMap Int -> Type -> TCEnv s Type
doInstantiate tvars ty = let
  keyNotFound = fromMaybe (error "panic: muvar not found")
  mapFn = let r = doInstantiate tvars in \case
--  THBound i   -> pure (0 `setBit` (tvarStart + i - IM.size muVars) , [])
    THBound i   -> pure (0 `setBit` (keyNotFound $ tvars IM.!? i)  , [])
    THMuBound i -> use muInstances >>= \muVars -> case muVars IM.!? i of
      Just m -> pure (0 `setBit` m , [])
      Nothing -> freshBiSubs 1 >>= \[mInst] -> (muInstances %= IM.insert i mInst) $> (0 `setBit` mInst , [])
    THBi{}      -> error $ "higher rank polymorphic instantiation"
    THMu m t    -> do -- µx.F(x) is to inference (x & F(x))
      use muInstances >>= \muVars -> do
        mInst <- case muVars IM.!? m of
          Nothing -> freshBiSubs 1 >>= \[mInst] -> mInst <$ (muInstances %= IM.insert m mInst)
          Just m -> pure m
        doInstantiate tvars t <&> \case
          TyGround g  -> (0 `setBit` mInst , g)
          TyVars vs g -> (vs `setBit` mInst , g)
    THTyCon t -> (\x -> (0 , [THTyCon x])) <$> case t of
      THArrow as ret -> THArrow   <$> (r `mapM` as) <*> (r ret)
      THProduct as   -> THProduct <$> (r `mapM` as)
      THTuple as     -> THTuple   <$> (r `mapM` as)
      THSumTy as     -> THSumTy   <$> (r `mapM` as)
    t -> pure (0 , [t])
  instantiateGround g = mapFn `mapM` g <&> unzip <&> \(tvars , ty) -> let
    tvs = foldr (.|.) 0 tvars
    groundTys = concat ty
    in if tvs == 0 then TyGround groundTys else TyVars tvs groundTys
  in case ty of 
    TyGround g -> instantiateGround g
    TyVars vs g -> mergeTypes True (TyVars vs []) <$> instantiateGround g -- TODO ! get the right polarity here
    TyVar v -> pure (TyVar v)

atomicBiSub :: TyHead -> TyHead -> TCEnv s BiCast
atomicBiSub p m = let tyM = TyGround [m] ; tyP = TyGround [p] in
 when global_debug (traceM ("⚛bisub: " <> prettyTyRaw tyP <> " <==> " <> prettyTyRaw tyM)) *>
 case (p , m) of
  (_ , THTop) -> pure (CastInstr MkTop)
  (THBot , _) -> pure (CastInstr MkBot)
  (THPrim p1 , THPrim p2) -> primBiSub p1 p2
  (THExt a , THExt b) | a == b -> pure BiEQ
  (p , THExt i) -> biSubType tyP     =<< fromJust . tyExpr . (`readPrimExtern` i) <$> use externs
  (THExt i , m) -> (`biSubType` tyM) =<< fromJust . tyExpr . (`readPrimExtern` i) <$> use externs

  -- Bound vars (removed at +THBi, so should never be encountered during biunification)
  (THBound i , x) -> error $ "unexpected THBound: " <> show i
  (x , THBound i) -> error $ "unexpected THBound: " <> show i
  (x , THBi nb y) -> error $ "unexpected THBi: "      <> show (p,m)

  (THBi nb p , m) -> do
    instantiated <- instantiate nb p
    biSubType instantiated tyM

  (THTyCon t1 , THTyCon t2) -> biSubTyCon p m (t1 , t2)

--(THPi (Pi p ty) , y) -> biSub ty [y]
--(x , THPi (Pi p ty)) -> biSub [x] ty
  (THSet u , x) -> pure BiEQ
  (x , THSet u) -> pure BiEQ

  (x , THTyCon THArrow{}) -> failBiSub (TextMsg "Excess arguments")       (TyGround [p]) (TyGround [m])
  (THTyCon THArrow{} , x) -> failBiSub (TextMsg "Insufficient arguments") (TyGround [p]) (TyGround [m])
  (a , b) -> failBiSub (TextMsg "Incompatible types") (TyGround [a]) (TyGround [b])

-- TODO cache THTycon contained vars?
getTVarsType = \case
  TyVar v -> setBit 0 v
  TyVars vs g -> foldr (.|.) vs (getTVarsTyHead <$> g)
  TyGround  g -> foldr (.|.) 0 (getTVarsTyHead <$> g)
getTVarsTyHead :: TyHead -> BitSet
getTVarsTyHead = \case
  THTyCon t -> case t of
    THArrow ars r -> foldr (.|.) 0 (getTVarsType r : (getTVarsType <$> ars) )
    THProduct   r -> foldr (.|.) 0 (getTVarsType <$> IM.elems r)
    THSumTy     r -> foldr (.|.) 0 (getTVarsType <$> IM.elems r)
    THTuple     r -> foldr (.|.) 0 (getTVarsType <$> r)
--THBi _ t -> getTVarsType t
  x -> 0

-- used for computing both differences between 2 IntMaps (alignWith doesn't give access to the ROnly map key)
data KeySubtype
  = LOnly Type       -- OK by record | sumtype subtyping
  | ROnly IName Type -- KO field not present (IName here is a field or label name)
  | Both  Type Type  -- biunify the leaf types

-- This is complicated slightly by needing to recover the necessary subtyping casts
biSubTyCon p m = let tyP = TyGround [p] ; tyM = TyGround [m] in \case
  (THArrow args1 ret1 , THArrow args2 ret2) -> arrowBiSub (args1,args2) (ret1,ret2)
  (THArrow ars ret ,  THSumTy x) -> pure BiEQ --_
  (THTuple x , THTuple y) -> BiEQ <$ V.zipWithM biSubType x y
  (THProduct x , THProduct y) -> let --use normFields >>= \nf -> let -- record: fields in the second must all be in the first
    merged     = IM.mergeWithKey (\k a b -> Just (Both a b)) (fmap LOnly) (IM.mapWithKey ROnly) x y
--  normalized = V.fromList $ IM.elems $ IM.mapKeys (nf VU.!) merged
    normalized = V.fromList $ IM.elems merged -- $ IM.mapKeys (nf VU.!) merged
    go leafCasts normIdx ty = case ty of
      LOnly a   {- drop     -} -> pure $ leafCasts --(field : drops , leafCasts)
      ROnly f a {- no subty -} -> leafCasts <$ failBiSub (AbsentField (QName f)) tyP tyM
      Both  a b {- leafcast -} -> biSubType a b <&> (\x -> (normIdx , x) : leafCasts) -- leaf bicast
    in V.ifoldM go [] normalized <&> \leafCasts ->
       let drops = V.length normalized - length leafCasts -- TODO rm filthy list length
       in if drops > 0
       then CastProduct drops leafCasts -- dropped some fields
       else let leaves = snd <$> leafCasts
       in if all (\case {BiEQ->True;_->False}) leaves then BiEQ else CastLeaves leaves
  (THSumTy x , THSumTy y) -> let
    go label subType = case y IM.!? label of -- y must contain supertypes of all x labels
      Nothing -> failBiSub (AbsentLabel (QName label)) tyP tyM
      Just superType -> biSubType subType superType
    in BiEQ <$ (go `IM.traverseWithKey` x) -- TODO bicasts
  (THSumTy s , THArrow args retT) | [(lName , tuple)] <- IM.toList s -> -- singleton sumtype => Partial application of Label
    let t' = TyGround $ case tuple of
               TyGround [THTyCon (THTuple x)] -> [THTyCon $ THTuple (x V.++ V.fromList args)]
               x                              -> [THTyCon $ THTuple (V.fromList (x : args))]
    in biSubType (TyGround [THTyCon (THSumTy $ IM.singleton lName t')]) retT
  (THSumTy s , THArrow{}) | [single] <- IM.toList s -> failBiSub (TextMsg "Note. Labels must be fully applied to avoid ambiguity") tyP tyM
  (a , b)         -> failBiSub TyConMismatch tyP tyM

arrowBiSub (argsp,argsm) (retp,retm) = let
  bsArgs [] [] = ([] , Nothing , ) <$> biSubType retp retm
  bsArgs x  [] = ([] , Just x  , ) <$> biSubType (prependArrowArgsTy x retp) retm  -- Partial application
  bsArgs []  x = ([] , Nothing , ) <$> biSubType retp (prependArrowArgsTy x retm)  -- Returns a function
  bsArgs (p : ps) (m : ms) = (\arg (xs,pap,retbi) -> (arg:xs , pap , retbi)) <$> biSubType m p <*> bsArgs ps ms
  in (\(argCasts, pap, retCast) -> CastApp argCasts pap retCast) <$> bsArgs argsp argsm

primBiSub p1 m1 = case (p1 , m1) of
  (PrimInt p , PrimInt m) -> if p == m then pure BiEQ else if m > p then pure (CastInstr Zext) else (BiEQ <$ failBiSub (TextMsg "Primitive Finite Int") (TyGround [THPrim p1]) (TyGround [THPrim m1]))
  (PrimInt p , PrimBigInt) -> pure (CastInstr (GMPZext p))
  (p , m) -> if (p /= m) then (failBiSub (TextMsg "primitive types") (TyGround [THPrim p1]) (TyGround [THPrim m1])) else pure BiEQ
