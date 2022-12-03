-- See presentation/TypeTheory for commentary
module BiUnify (bisub) where
import Prim (PrimInstr(..) , PrimType(..))
import CoreSyn as C
import Errors ( BiFail(..), TmpBiSubError(TmpBiSubError) )
import CoreUtils
import TCState
import PrettyCore (prettyTyRaw)
import Externs (readPrimExtern)
import Data.Distributive
import qualified BitSetMap as BSM ( (!?), elems, mergeWithKey', singleton, toList, traverseWithKey )
import qualified Data.Vector.Mutable as MV ( read, write )
import qualified Data.Vector as V ( Vector, (!), (++), fromList, ifoldM, length, zipWithM )
import Data.Functor.Foldable
import Control.Lens ( use, (%=) )
debug_biunify = global_debug

-- First class polymorphism:
-- \i ⇒ if (i i) true then true else true
-- i used as:
-- i : (i1 -> i1) -> (i1 -> i1)
-- i : i1 -> i1
-- ⇒ Need to consider i may be polymorphic
-- i : a -> a

-- inferred type: a & (a -> i1 -> i1) -> i1
-- contravariant recursive type; this only makes sense if a is higher rank polymorphic:
-- a & (a -> i1 -> i1) ⇒ (Π B -> B -> B)

failBiSub ∷ BiFail -> Type -> Type -> TCEnv s BiCast
failBiSub msg a b = BiEQ <$ (tmpFails %= (TmpBiSubError msg a b:))

leakVars :: Int -> BitSet -> TCEnv s () -- v <=> a -> b => set a and b to lvl of v (they're exported outwards)
leakVars v export = let
  go [] = []
--go (l : lvs) = (l .|. export) : (if testBit l v then lvs else go lvs)
  go (l : lvs) = if testBit l v
    then (l .|. export) : go lvs -- ! V belongs to higher lvl , add exports until v no longer present (which lvl?) 
    else l : lvs -- OK v is local
  in {-d_ (v , bitSet2IntList export) $-} lvls %= \case
    [] -> error "internal failure to initialise tvar lvls"
    l -> go l

leakTyVars v t = -- traceM (show v <> " " <> prettyTyRaw t) *>
  leakVars v (getTVarsType t) -- TODO avoid type traversal?

bisub a b = --when debug_biunify (traceM ("bisub: " <> prettyTyRaw a <> " ⇔ " <> prettyTyRaw b)) *>
  biSubType a b

biSubTVars ∷ BitSet -> BitSet -> TCEnv s BiCast
biSubTVars p m = BiEQ <$ (bitSet2IntList p `forM` \v -> biSubTVarTVar v `mapM` bitSet2IntList m)

biSubTVarTVar p m = use bis >>= \v -> MV.read v p >>= \(BiSub p' m') -> do
  when debug_biunify (traceM ("bisubττ: " <> prettyTyRaw (TyVar p) <> " ⇔ " <> prettyTyRaw (TyVar m)))
  leakVars p (0 `setBit` m)
  leakVars m (0 `setBit` p)
  MV.write v p (BiSub (mergeTVar m p') (mergeTVar m m')) -- TODO is ok? intended to fix recursive type unification
  unless (hasVar m' m) $ void (biSubType p' (TyVar m)) -- Avoid loops
  pure BiEQ

biSubTVarP v m = use bis >>= \b -> MV.read b v >>= \(BiSub p' m') -> do
  let mMerged = mergeTypes True m m'
  when debug_biunify (traceM ("bisub: " <> prettyTyRaw (TyVar v) <> " ⇔ " <> prettyTyRaw m))
  leakTyVars v m
  MV.write b v (BiSub p' mMerged)
  if mMerged == m' then pure BiEQ -- if merging was noop, this would probably loop
  else biSubType p' m

biSubTVarM p v = use bis >>= \b -> MV.read b v >>= \(BiSub p' m') -> do
  let pMerged = mergeTypes False p p'
  when debug_biunify (traceM ("bisub: " <> prettyTyRaw p <> " ⇔ " <> prettyTyRaw (TyVar v)))
  leakTyVars v p
  MV.write b v (BiSub pMerged m')
  if pMerged == p' then pure BiEQ -- if merging was noop, this would probably loop
  else biSubType p m'

biSubType ∷ Type -> Type -> TCEnv s BiCast
biSubType tyP tyM = let
  (pVs , pTs) = partitionType tyP
  (mVs , mTs) = partitionType tyM
  in do
  void (biSubTVars pVs mVs)
  unless (null mTs) $ bitSet2IntList pVs `forM_` \v -> biSubTVarP v (TyGround mTs)
  unless (null pTs) $ bitSet2IntList mVs `forM_` \v -> biSubTVarM (TyGround pTs) v
  biSub pTs mTs

-- bisub on ground types
biSub ∷ [TyHead] -> [TyHead] -> TCEnv s BiCast
biSub a b = case (a , b) of
  ([] ,  _)  -> pure BiEQ
  (_  , [])  -> pure BiEQ
  (p , m)    -> BiEQ <$ (p `forM` \aP -> atomicBiSub aP `mapM` m)

-- Instantiation; substitute quantified variables with fresh type vars;
-- Note. weird special case (A & {f : B}) typevars as produced by lens over
--   The A serves to propagate the input record, minus the lens field
--   what is meant is really set difference: A =: A // { f : B }
instantiate :: Bool -> Int -> Type -> TCEnv s Type
instantiate pos nb ty = (if nb == 0 then pure mempty else freshBiSubs nb <&> V.fromList)
  <&> \tvars -> snd $ cata (instantiateF tvars) ty pos

-- Replace THBound with new tvars and record the new recursive tvars spawned (for generalise)
instantiateF :: V.Vector Int -> TypeF (Bool -> (BitSet , Type)) -> Bool -> (BitSet , Type)
instantiateF tvars t pos = let
  instGround :: THead (Bool -> (BitSet , Type)) -> (BitSet , Type)
  instGround = let thBound i = (0 , TyVar (tvars V.! i)) in \case -- (0 `setBit` (tvars V.! i) , []) in \case
    THMu m t    -> let mInst = tvars V.! m in -- µx.F(x) is to inference (x & F(x))
      case t pos of
        (rs , TyGround g ) -> (setBit rs m , TyVars (0 `setBit` mInst) g)
        (rs , TyVars vs g) -> (setBit rs m , TyVars (vs `setBit` mInst) g)
        _ -> _
    THBound i   -> thBound i
    THMuBound i -> thBound i
    THBi{}      -> error $ "higher rank polymorphic instantiation"
    t -> let x = distribute t pos in (getRecs x , TyGround [snd <$> x])
  getRecs :: Foldable t => t (BitSet , a) -> BitSet
  getRecs = foldr (\a b -> fst a .|. b) 0
  in case t of
  TyVarsF vs g -> let x = instGround <$> g in (getRecs x , mergeTypeList pos (TyVars vs [] : (snd <$> x)))
  TyGroundF g  -> let x = instGround <$> g in (getRecs x , mergeTypeList pos (snd <$> x))
  t -> distribute t pos & \x -> (getRecs x , embed (fmap snd x))

atomicBiSub ∷ TyHead -> TyHead -> TCEnv s BiCast
atomicBiSub p m = let tyM = TyGround [m] ; tyP = TyGround [p] in
 when debug_biunify (traceM ("⚛bisub: " <> prettyTyRaw tyP <> " ⇔ " <> prettyTyRaw tyM)) *>
 case (p , m) of
  (_ , THTop) -> pure (CastInstr MkTop)
  (THBot , _) -> pure (CastInstr MkBot)
  (THPrim p1 , THPrim p2) -> primBiSub p1 p2
  (THExt a , THExt b) | a == b -> pure BiEQ
  (_ , THExt i) -> biSubType tyP     =<< fromJust . tyExpr . (`readPrimExtern` i) <$> use externs
  (THExt i , _) -> (`biSubType` tyM) =<< fromJust . tyExpr . (`readPrimExtern` i) <$> use externs

  -- Bound vars (removed at +THBi, so should never be encountered during biunification)
  (THBound i , _) -> error $ "unexpected THBound: " <> show i
  (_ , THBound i) -> error $ "unexpected THBound: " <> show i
  (_ , THBi{}   ) -> error $ "unexpected THBi: "    <> show (p , m)
  (t@THMu{} , y) -> instantiate True 0 (TyGround [t]) >>= \x -> biSubType x (TyGround [y]) -- TODO not ideal
  (x , t@THMu{}) -> instantiate True 0 (TyGround [t]) >>= \y -> biSubType (TyGround [x]) y   -- printList Nil ⇒ [Nil] <:? µx.[Nil | Cons {%i32 , x}]
--(x , THMuBound m) -> use muUnrolls >>= \m -> _ -- printList (Cons 3 Nil) ⇒ [Nil] <:? x

  (THBi nb p , _) -> do
    instantiated ← instantiate True nb p -- TODO polarity ok?
    biSubType instantiated tyM

  (THTyCon t1 , THTyCon t2) -> biSubTyCon p m (t1 , t2)

--(THPi (Pi p ty) , y) -> biSub ty [y]
--(x , THPi (Pi p ty)) -> biSub [x] ty
  (THSet _u , _) -> pure BiEQ
  (_ , THSet _u) -> pure BiEQ

  (_ , THTyCon THArrow{}) -> failBiSub (TextMsg "Excess arguments")       (TyGround [p]) (TyGround [m])
  (THTyCon THArrow{} , _) -> failBiSub (TextMsg "Insufficient arguments") (TyGround [p]) (TyGround [m])
  (a , b) -> failBiSub (TextMsg "Incompatible types") (TyGround [a]) (TyGround [b])

-- TODO cache THTycon contained vars?
getTVarsType = \case
  TyVar v -> setBit 0 v
  TyVars vs g -> foldr (.|.) vs (getTVarsTyHead <$> g)
  TyGround  g -> foldr (.|.) 0 (getTVarsTyHead <$> g)
  _ -> error "panic: getTVars on non-trivial type"
getTVarsTyHead ∷ TyHead -> BitSet
getTVarsTyHead = \case
  THTyCon t -> case t of
    THArrow ars r -> foldr (.|.) 0 (getTVarsType r : (getTVarsType <$> ars) )
    THProduct   r -> foldr (.|.) 0 (getTVarsType <$> BSM.elems r)
    THSumTy     r -> foldr (.|.) 0 (getTVarsType <$> BSM.elems r)
    THTuple     r -> foldr (.|.) 0 (getTVarsType <$> r)
    _ -> _
--THBi _ t -> getTVarsType t
  _ -> 0

-- used for computing both differences between 2 IntMaps (alignWith doesn't give access to the ROnly map key)
data KeySubtype
  = LOnly Type       -- OK by record | sumtype subtyping
  | ROnly IName Type -- KO field not present (IName here is a field or label name)
  | Both  Type Type  -- biunify the leaf types

-- This is complicated slightly by needing to recover the necessary subtyping casts
biSubTyCon p m = let tyP = TyGround [p] ; tyM = TyGround [m] in \case
  (THArrow args1 ret1 , THArrow args2 ret2) -> arrowBiSub (args1,args2) (ret1,ret2)
  (THTuple x , THTuple y) -> BiEQ <$ V.zipWithM biSubType x y
  (THProduct x , THProduct y) -> let --use normFields >>= \nf -> let -- record: fields in the second must all be in the first
    merged     = BSM.mergeWithKey' (\_k a b -> Just (Both a b)) (\_k v -> LOnly v) (ROnly) x y
--  merged     = BSM.mergeWithKey (\k a b -> Just (Both a b)) (fmap LOnly) (BSM.mapWithKey ROnly) x y
--  merged     = BSM.mergeWithKey (\k a b -> Both a b) (const LOnly) (ROnly) x y
--  normalized = V.fromList $ IM.elems $ IM.mapKeys (nf VU.!) merged
    normalized = BSM.elems merged -- $ IM.mapKeys (nf VU.!) merged
    go leafCasts normIdx ty = case ty of
      LOnly _a   {- drop     -} -> pure $ leafCasts --(field : drops , leafCasts)
      ROnly f _a {- no subty -} -> leafCasts <$ failBiSub (AbsentField (QName f)) tyP tyM
      Both  a b  {- leafcast -} -> biSubType a b <&> (\x -> (normIdx , x) : leafCasts) -- leaf bicast
    in V.ifoldM go [] normalized <&> \leafCasts ->
       let drops = V.length normalized - length leafCasts -- TODO rm filthy list length
       in if drops > 0
       then CastProduct drops leafCasts -- dropped some fields
       else let leaves = snd <$> leafCasts
       in if all (\case {BiEQ->True;_->False}) leaves then BiEQ else CastLeaves leaves
  (THSumTy x , THSumTy y) -> let
    go label subType = case y BSM.!? label of -- y must contain supertypes of all x labels
      Nothing -> failBiSub (AbsentLabel (QName label)) tyP tyM
      Just superType -> biSubType subType superType
    in BiEQ <$ (go `BSM.traverseWithKey` x) -- TODO bicasts
  (THSumTy s , THArrow args retT) | [(lName , tuple)] ← BSM.toList s -> -- singleton sumtype ⇒ Partial application of Label
    let t' = TyGround $ case tuple of
               TyGround [THTyCon (THTuple x)] -> [THTyCon $ THTuple (x V.++ V.fromList args)]
               x                              -> [THTyCon $ THTuple (V.fromList (x : args))]
    in biSubType (TyGround [THTyCon (THSumTy $ BSM.singleton lName t')]) retT
  (THSumTy s , THArrow{}) | [_single] ← BSM.toList s -> failBiSub (TextMsg "Note. Labels must be fully applied to avoid ambiguity") tyP tyM
  _         -> failBiSub TyConMismatch tyP tyM

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
