-- See presentation/TypeTheory for commentary
{-# LANGUAGE TemplateHaskell #-}
module BiUnify (biSubTVarTVar , biSubType , BisubEnv , BisubEnvState(..)) where
import Prim (PrimInstr(..) , PrimType(..))
import CoreSyn as C
import Errors ( BiFail(..), TmpBiSubError(TmpBiSubError) )
import CoreUtils (prependArrowArgsTy , tHeadToTy , mergeTypeList , partitionType , mergeTypes , mergeTVar , hasVar)
import PrettyCore (prettyTyRaw)
import Builtins (readPrimType)
import Data.Distributive (distribute)
import qualified BitSetMap as BSM ( (!?), elems, mergeWithKey', singleton, toList, traverseWithKey )
import qualified Data.Vector as V ( Vector, (!), (++), fromList, ifoldM, length, zipWithM )
import Data.Functor.Foldable
import Control.Lens ( makeLenses , use , (%=) , (.=) )
import qualified Data.Vector.Mutable as MV
debug_biunify = global_debug

resolveTypeQName = _ -- TCState.resolveTypeQName

type BisubEnv s a = StateT (BisubEnvState s) (ST s) a
data BisubEnvState s = BisubEnvState
 { _blen     :: Int                -- cursor for bis which may have spare space
 , _bis      :: MV.MVector s BiSub -- typeVars
 , _tmpFails :: [TmpBiSubError]    -- bisub failures are dealt with at an enclosing App
 }; makeLenses ''BisubEnvState

-- spawn new tvar slots in the bisubs vector
-- TODO this fn is duplicated !
freshBiSubs :: Int -> BisubEnv s [Int]
freshBiSubs n = do
  bisubs <- use bis
  biLen  <- use blen
  let tyVars  = [biLen .. biLen+n-1]
  blen .= biLen + n
  bisubs <- if MV.length bisubs < biLen + n then MV.grow bisubs n else pure bisubs
  bis .= bisubs
  tyVars `forM_` \i -> MV.write bisubs i (BiSub tyBot tyTop)
  pure tyVars

failBiSub :: BiFail -> Type -> Type -> BisubEnv s BiCast
failBiSub msg a b = BiEQ <$ (tmpFails %= (TmpBiSubError msg a b:))

biSubTVars :: BitSet -> BitSet -> BisubEnv s BiCast
biSubTVars p m = BiEQ <$ (bitSet2IntList p `forM` \v -> biSubTVarTVar v `mapM` bitSet2IntList m)

biSubTVarTVar p m = use bis >>= \v -> MV.read v p >>= \(BiSub p' m') -> do
  when debug_biunify (traceM ("bisubττ: " <> prettyTyRaw (tyVar p) <> " <=> " <> prettyTyRaw (tyVar m)))
  MV.write v p (BiSub (mergeTVar m p') (mergeTVar m m')) -- TODO is ok? intended to fix recursive type unification
  if hasVar m' m then pure BiEQ else biSubType p' (TyVars (setBit 0 m) []) -- Avoid loops

biSubTVarP v m = use bis >>= \b -> MV.read b v >>= \(BiSub p' m') -> do
  let mMerged = mergeTypes True m m'
  when debug_biunify (traceM ("bisub: " <> prettyTyRaw (tyVar v) <> " <=> " <> prettyTyRaw m))
  MV.write b v (BiSub p' mMerged)
  if mMerged == m' then pure BiEQ -- if merging was noop, this would probably loop
  else biSubType p' m

biSubTVarM p v = use bis >>= \b -> MV.read b v >>= \(BiSub p' m') -> do
  let pMerged = mergeTypes False p p'
  when debug_biunify (traceM ("bisub: " <> prettyTyRaw p <> " <=> " <> prettyTyRaw (TyVars (setBit 0 v) [])))
  MV.write b v (BiSub pMerged m')
  if pMerged == p' then pure BiEQ -- if merging was noop, this would probably loop
  else biSubType p m'

-- when debug_biunify (traceM ("bisub: " <> prettyTyRaw a <> " <=> " <> prettyTyRaw b)) *>
biSubType :: Type -> Type -> BisubEnv s BiCast
biSubType tyP tyM = let
  (pVs , pTs) = partitionType tyP
  (mVs , mTs) = partitionType tyM
  in do
  void (biSubTVars pVs mVs)
  unless (null mTs) $ bitSet2IntList pVs `forM_` \v -> biSubTVarP v (TyGround mTs)
  unless (null pTs) $ bitSet2IntList mVs `forM_` \v -> biSubTVarM (TyGround pTs) v
  biSub pTs mTs

isBiEq = \case { BiEQ -> True ; _ -> False }

-- bisub on ground types
biSub :: [TyHead] -> [TyHead] -> BisubEnv s BiCast
biSub a b = case (a , b) of
  ([] ,  _)  -> pure BiEQ
  (_  , [])  -> pure BiEQ
  (p , m)    -> (p `forM` \aP -> atomicBiSub aP `mapM` m)
    <&> \casts -> case mergeCasts $ dropWhile isBiEq (concat casts) of
    x : xs -> if all isBiEq xs then x else error $ "TODO: cast merge: " <> show (x : xs)
    [] -> BiEQ

mergeCasts :: [BiCast] -> [BiCast]
mergeCasts (x : xs) = let
  mergeCast (CastZext n) ((CastZext m) : xs) = CastZext (max n m) : xs
  mergeCast a b = a : b
  in foldr mergeCast [x] xs
mergeCasts [] = []

-- Instantiation; substitute quantified variables with fresh type vars;
-- Note. weird special case (A & {f : B}) typevars as produced by lens over
--   The A serves to propagate the input record, minus the lens field
--   what is meant is really set difference: A =: A // { f : B }
instantiate :: Bool -> Int -> Type -> BisubEnv s Type
instantiate pos nb ty = (if nb == 0 then pure mempty else freshBiSubs nb <&> V.fromList)
  <&> \tvars -> snd $ cata (instantiateF tvars) ty pos

-- Replace THBound with new tvars and record the new recursive tvars spawned (for generalise)
instantiateF :: V.Vector Int -> TypeF (Bool -> (BitSet , Type)) -> Bool -> (BitSet , Type)
instantiateF tvars t pos = let
  instGround :: THead (Bool -> (BitSet , Type)) -> (BitSet , Type)
  instGround = let thBound i = (0 , TyVars (setBit 0 (tvars V.! i)) []) in \case
    THMu m t    -> let mInst = tvars V.! m in -- µx.F(x) is to inference (x & F(x))
      case t pos of
        (rs , TyGround g ) -> (setBit rs m , TyVars (0 `setBit` mInst) g)
        (rs , TyVars vs g) -> (setBit rs m , TyVars (vs `setBit` mInst) g)
    THBound i   -> thBound i
    THMuBound i -> thBound i
    THBi n _    -> error $ "higher rank polymorphic instantiation: " <> show n
    t -> let x = distribute t pos in (getRecs x , TyGround [snd <$> x])
  getRecs :: Foldable t => t (BitSet , a) -> BitSet
  getRecs = foldr (\a b -> fst a .|. b) 0
  in case t of
  TyVarsF vs g -> let x = instGround <$> g in (getRecs x , mergeTypeList pos (TyVars vs [] : (snd <$> x)))
  TyGroundF g  -> let x = instGround <$> g in (getRecs x , mergeTypeList pos (snd <$> x))

atomicBiSub :: TyHead -> TyHead -> BisubEnv s BiCast
atomicBiSub p m = let tyM = TyGround [m] ; tyP = TyGround [p] in
 when debug_biunify (traceM ("⚛bisub: " <> prettyTyRaw tyP <> " <=> " <> prettyTyRaw tyM)) *>
 case (p , m) of
  (THSet up , THSet um) | up <= um -> pure BiEQ
  (_ , THTop) -> pure (CastInstr MkTop)
  (THBot , _) -> pure (CastInstr MkBot)
  (THPrim p1 , THPrim p2) -> primBiSub p1 p2
  (THExt a , THExt b) | a == b -> pure BiEQ
  (_ , THExt i) -> biSubType tyP     $ exprType (readPrimType i)
  (THExt i , _) -> (`biSubType` tyM) $ exprType (readPrimType i)
  (_ , THAlias q) -> resolveTypeQName q >>= \m -> biSubType (tHeadToTy p) m
  (THAlias q , _) -> resolveTypeQName q >>= \p -> biSubType p (tHeadToTy m)

  -- Bound vars (removed at +THBi, so should never be encountered during biunification)
  (THBound i , _) -> error $ "unexpected THBound: " <> show i
  (_ , THBound i) -> error $ "unexpected THBound: " <> show i
  (_ , THBi{}   ) -> error $ "unexpected THBi: "    <> show (p , m) -- shouldn't exist on the right
  (THBi nb p , _) -> do
    instantiated <- instantiate True nb p -- TODO polarity ok?
    biSubType instantiated tyM
  (t@THMu{} , y) -> instantiate True 0 (TyGround [t]) >>= \x -> biSubType x (TyGround [y]) -- TODO not ideal
  (x , t@THMu{}) -> instantiate True 0 (TyGround [t]) >>= \y -> biSubType (TyGround [x]) y   -- printList Nil ⇒ [Nil] <:? µx.[Nil | Cons {%i32 , x}]
--(x , THMuBound m) -> use muUnrolls >>= \m -> _ -- printList (Cons 3 Nil) ⇒ [Nil] <:? x

  (THTyCon t1 , THTyCon t2) -> biSubTyCon p m (t1 , t2)
  (_ , THTyCon THArrow{}) -> failBiSub (TextMsg "Excess arguments")       (TyGround [p]) (TyGround [m])
  (THTyCon THArrow{} , _) -> failBiSub (TextMsg "Insufficient arguments") (TyGround [p]) (TyGround [m])
  (a , b) -> failBiSub (TextMsg "Incompatible types") (TyGround [a]) (TyGround [b])

-- used for computing both differences between 2 IntMaps (alignWith doesn't give access to the ROnly map key)
data KeySubtype
  = LOnly Type       -- OK by record | sumtype subtyping
  | ROnly IName Type -- KO field not present (IName here is a field or label name)
  | Both  Type Type  -- biunify the leaf types
  deriving Show

-- This is complicated slightly by needing to recover the necessary subtyping casts
biSubTyCon p m = let tyP = TyGround [p] ; tyM = TyGround [m] in \case
  (THArrow args1 ret1 , THArrow args2 ret2) -> arrowBiSub (args1 , args2) (ret1 , ret2)
  (THTuple x , THTuple y) -> BiEQ <$ V.zipWithM biSubType x y
  (THArray x , THArray y) -> BiEQ <$ biSubType x y
  (THProduct x , THProduct y) -> let
    merged     = BSM.mergeWithKey' (\_k a b -> Just (Both a b)) (\_k v -> LOnly v) ROnly x y
    normalized = BSM.elems merged -- $ IM.mapKeys (nf VU.!) merged
    go leafCasts normIdx ty = case ty of
      LOnly _a   {- drop     -} -> pure leafCasts --(field : drops , leafCasts)
      ROnly f _a {- no subty -} -> leafCasts <$ failBiSub (AbsentField (QName f)) tyP tyM
      Both  a b  {- leafcast -} -> biSubType a b <&> (\x -> (normIdx , x) : leafCasts) -- leaf bicast
    in V.ifoldM go [] normalized <&> \leafCasts ->
       let drops = V.length normalized - length leafCasts -- TODO rm filthy list length
       in if drops > 0
       then CastProduct drops leafCasts -- dropped some fields
       else let leaves = snd <$> leafCasts
       in if all (\case {BiEQ->True;_->False}) leaves then BiEQ else CastFields leaves
  (THSumTy _ , THSumOpen _) -> pure BiEQ -- open sums can match everything
  (THSumTy x , THSumTy y) -> let
    go label subType = case y BSM.!? label of -- x must contain supertypes of all x labels
      Nothing -> failBiSub (AbsentLabel (QName label)) tyP tyM
      Just superType -> biSubType subType superType
-- TODO insert Sum->Sum casts (This is were labels are actually written to memory)
--  merged = BSM.mergeWithKey' (\_k a b -> Just (Both a b)) (\_k v -> LOnly v) ROnly x y
    in BiEQ <$ (go `BSM.traverseWithKey` x)
  (THSumTy s , THArrow args retT) | [(lName , tuple)] <- BSM.toList s -> -- singleton sumtype ⇒ Partial application of Label
    let t' = TyGround $ case tuple of
               TyGround [THTyCon (THTuple x)] -> [THTyCon $ THTuple (x V.++ V.fromList args)]
               x                              -> [THTyCon $ THTuple (V.fromList (x : args))]
    in biSubType (TyGround [THTyCon (THSumTy $ BSM.singleton lName t')]) retT
  (THSumTy s , THArrow{}) | [_single] <- BSM.toList s -> failBiSub (TextMsg "Note. Partially applied Label") tyP tyM
  _         -> failBiSub TyConMismatch tyP tyM

arrowBiSub (argsp,argsm) (retp,retm) = let
  bsArgs [] [] = ([] , Nothing , ) <$> biSubType retp retm
  bsArgs x  [] = ([] , Just x  , ) <$> biSubType (prependArrowArgsTy x retp) retm  -- Partial application
  bsArgs []  x = ([] , Nothing , ) <$> biSubType retp (prependArrowArgsTy x retm)  -- Returns a function
  bsArgs (p : ps) (m : ms) = (\arg (xs,pap,retbi) -> (arg:xs , pap , retbi)) <$> biSubType m p <*> bsArgs ps ms
  in bsArgs argsp argsm <&> \(argCasts, pap, retCast) -> -- TODO keep the papCast ?
    if all isBiEq argCasts && isNothing pap
    then retCast
--  else CastApp argCasts {- pap -} Nothing retCast
    else CastApp argCasts pap retCast

primBiSub p1 m1 = case (p1 , m1) of
  (PrimInt p , PrimInt m) -> case compare p m of
    EQ -> pure BiEQ
    LT -> pure (CastZext m)
    GT -> BiEQ <$ failBiSub (TextMsg "Primitive Finite Int") (TyGround [THPrim p1]) (TyGround [THPrim m1])
--(PrimInt p , PrimBigInt) -> pure (CastInstr (GMPZext p))
  (p , m) -> if p /= m then failBiSub (TextMsg "primitive types") (TyGround [THPrim p1]) (TyGround [THPrim m1]) else pure BiEQ
