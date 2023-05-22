{-# Language TemplateHaskell #-}
module Generalise (generalise) where
import Control.Lens
import CoreSyn
import CoreUtils
import PrettyCore
import TCState
import MuRoll
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector as V
import Data.Functor.Foldable

-- TODO recursives doesn't account for μ-roll μ-merges
debug_gen = False

type Cooc = (Maybe Type , Maybe Type)
data VarSub = SubVar Int | SubTy Type | DeleteVar | GeneraliseVar | RecursiveVar deriving (Show , Eq)
data Acc = Acc { _deletes :: BitSet , _subTys :: (BitSet , [Type]) , _subVars :: [(Int , Int)] }; makeLenses ''Acc

-- Generalising a type unavoidably requires a double pass since simplification must know all co-occurences
-- 1. recursively read tvar bounds and register coocurrences
-- 2. re-read all tvar bounds, this time merging according to cooccurence analysis
-- 3. Finally tighten μ-types (cata: thus can hyloM 2 and 3)
generalise :: forall s. Type -> TCEnv s Type
generalise startType = do
  recursives .= 0
  bl    <- use blen
  bis'  <- use bis
  coocV <- MV.replicate bl (Nothing , Nothing)
  rawT  <- buildCoocs bis' coocV 0 True startType
  recs    <- use recursives
  coocVF  <- V.unsafeFreeze coocV
  let varSubs = buildVarSubs coocVF recs
  MV.replicate (MV.length bis') (complement 0) >>= (genVec .=) -- len bis' is more than enough space for gens
  nquants .= 0
  when debug_gen $ do
    traceM ("raw-gen: " <> prettyTyRaw rawT)
    traceM $ "recs: " <> show (bitSet2IntList recs)
    --let recTypes = (\i -> (\(a , b) -> (i , fromMaybe _ (a <|> b))) (coocVF V.! i)) <$> bitSet2IntList recs
    --traceM $ "recTypes:\n" <> (unlines $ (\(i , t) -> show i <> ": " <> prettyTyRaw t) <$> recTypes)
    --rTs <- recTypes `forM` \(i , t) -> (i,) <$> buildType bis' varSubs 0 True t
    --traceM $ "rTs:\n" <> (unlines $ (\(i , t) -> show i <> ": " <> prettyTyRaw t) <$> rTs)
    --traceM (unlines $ V.toList $ show <$> V.indexed coocVF)
    --traceM (unlines $ V.toList $ show <$> V.indexed varSubs)

  done <- buildType bis' (varSubs V.!) 0 True rawT
--done <- reconstructType bis' varSubs startType
  let rolled = forgetRoll (cata rollType done)
  use nquants <&> \case { 0 -> rolled ; n -> TyGround [THBi n rolled] }

buildVarSubs coocV recs = V.constructN (V.length coocV) $ \prevSubs -> let
  v = V.length prevSubs
  prevTVs = setNBits v :: Integer -- don't redo co-occurence on prev-vars
  in case coocV V.! v of
  -- in v+v- if non-recursive v coocs with w then it always does, so "unify v with w" means "remove v"
  -- but in v+w+ or v-w- no shortcuts: "unify v with w" means "replace occurs of v with w"
  -- ! recursive vars are not necessarily strictly polar: eg. squish (@Node x ts) xs = Cons x (foldr squish xs ts)
  (Just x , Just y) -> partitionType (intersectTypes x y) & \(vs , ts) -> let
    genVar = if testBit recs v then RecursiveVar else GeneraliseVar
    xv = getTyVars x ; yv = getTyVars y
    xx = if clearBit xv v == 0 then yv else 0 ; yy = if clearBit yv v == 0 then xv else 0
    canSub w = prevSubs V.! w & \vs -> vs == genVar {-same recursivity-} -- || vs == RecursiveVar 
    subCandidates = (vs .|. xx .|. yy) .&. prevTVs
    in case find canSub (bitSet2IntList subCandidates) of
      Just w  -> SubVar w & (if debug_gen then d_ (v , w) else identity) -- TODO follow the vars
      Nothing -> if null ts then genVar else SubTy (TyGround ts)
  (polarP , polarN) -> let
    recCoocs = prevTVs .&. recs .&. (fromMaybe 0 ((fst . partitionType) <$> (polarP <|> polarN)))
    in if testBit recs v && recCoocs == 0 then RecursiveVar else DeleteVar -- TODO cant delete merge of recursive vars?!

--handleVar (deletes , (subMask , subTys) , recs) v
--  | testBit deletes v = DeleteVar
--  | testBit recs v    = RecursiveVar
--  | testBit subMask v = SubTy (subTys V.! popCount (subMask .&. setNBits v))
--  | otherwise         = GeneraliseVar

-- Support forward substitution
--buildVarSubs2 :: V.Vector Cooc -> BitSet -> (BitSet , (BitSet , V.Vector Type) , BitSet)
--buildVarSubs2 coocV recs = let
--  doVar :: Int -> Acc -> Cooc -> Acc
--  doVar v acc vCoocs = case vCoocs of
--    (Just x , Just y) -> partitionType (intersectTypes x y) & \(vs , ts) -> let
--      polarCooc a b = if clearBit (getTyVars a) v == 0 then getTyVars b else 0
--      subCandidates = let sameRec = if testBit recs v then (.&. recs) else (.&. complement recs)
--        in clearBit (sameRec (vs .|. polarCooc x y .|. polarCooc y x)) v -- .&. setNBits v
--      in case head (bitSet2IntList subCandidates) of
--        Just w  -> acc & subVars %~ ((v , w) :)
--        Nothing -> if null ts then acc else acc & subTys %~ \(mask , tys) -> (setBit mask v , TyGround ts : tys)
--    (polarP , polarN) -> let
--      recCoocs = recs .&. (fromMaybe 0 ((fst . partitionType) <$> (polarP <|> polarN)))
--      in if recCoocs /= 0 then acc else acc & deletes %~ (`setBit` v)
--  in ifoldl' doVar (Acc 0 (0 , []) []) coocV & \(Acc deletes subTys subVars) -> let
--    -- The trouble is eliminating subVars while avoiding cycles
--    -- Refusing to sub v for w when w > v doesn't simplify all (eg. scanSum is left with a polar tvar)
--    findSub :: forall s. MV.MVector s Int -> BitSet BitSet -> Int -> (BitSet , a) -> ST s (BitSet , a)
--    findSub subsV svmask stack v (dels , (smask,_))
--      | testBit stack v = pure (dels .|. stack , smask) -- leave one var (w) be generalised
--      | testBit dels  v = pure (setBit dels w .|. stack , smask)
--      | testBit smask v = _ -- insert a subty ?!
--      | testBit svmask v = MV.read subsV v >>= \w -> findSub (setBit stack v) w (dels , smask)
--      | True = _
--    in runST $ do
--    subsV <- MV.new (V.length coocV) -- sparse vector of varsubs
--    subs <- subVars `forM` \(v,w) -> v <$ MV.write subsV v w
--    foldM (\acc v -> findSub svmask subsV 0 v acc) (deletes , subTys) subs
--    <&> \(d , (smask , subs)) -> (deletes , (smask , V.fromList (reverse subs)) , recs)

-- build cooc-vector and mark recursive type variables
buildCoocs :: forall s. MV.MVector s BiSub -> MV.MVector s Cooc -> BitSet -> Bool -> Type -> TCEnv s Type
buildCoocs bis' coocV guards pos = let
  b = buildCoocs bis' coocV
  go loops (vs , gs) = do
    let l = loops .|. vs
    varBounds <- bitSet2IntList (vs .&. complement loops) `forM` \v ->
      MV.read bis' v >>= \(BiSub p m) -> go l (partitionType $ if pos then p else m)
    grounds <- gs `forM` \case
      THTyCon (THArrow ars ret) -> fmap THTyCon $ THArrow <$> (b l (not pos) `mapM` ars) <*> b l pos ret
      t -> b l pos `mapM` t -- TODO (?) THBi and THMu in here and don't guard recursive types!
    let ret = mergeTypeList pos (tyVars vs grounds : varBounds) -- Which vars can be dropped / generalised?
    partitionType ret & \(ws , gs) -> (recursives %= (.|. (ws .&. guards))) *>
      bitSet2IntList ws `forM_` \w ->
        MV.modify coocV (over (if pos then _1 else _2) (Just . maybe (TyVars ws gs) (unionTypes (TyVars ws gs)))) w
    pure ret
  in go guards . partitionType

generaliseVar :: Int -> TCEnv s Int
generaliseVar v = use genVec >>= \mp -> MV.read mp v >>= \perm -> if perm /= complement 0 then pure perm else do
  q <- nquants <<%= (1+)
  q <$ MV.write mp v q <* when debug_gen (traceM $ show v <> " => ∀" <> toS (number2CapLetter q))

-- reconstruct type using inferred bounds and co-occurence analysis
buildType :: forall s. MV.MVector s BiSub -> (Int -> VarSub) -> BitSet -> Bool -> Type -> TCEnv s Type
buildType bis' handleVar loops pos = let
  readBounds :: BitSet -> (BitSet , GroundType) -> TCEnv s Type
  readBounds loops (vs , gs) = do
    let l = loops .|. vs
        b = buildType bis' handleVar
    grounds <- gs `forM` \case
      THTyCon (THArrow ars ret) -> fmap THTyCon $ THArrow <$> (b l (not pos) `mapM` ars) <*> b l pos ret
      t -> b l pos `mapM` t
    varBounds <- bitSet2IntList (vs .&. complement loops) `forM` \v ->
      MV.read bis' v >>= \(BiSub p m) -> readBounds l (partitionType $ if pos then p else m)
    -- The big question is which vars to drop / sub
    subs <- bitSet2IntList vs `forM` \v -> case handleVar v of
      DeleteVar     -> pure tyBot
      GeneraliseVar -> generaliseVar v <&> \b -> TyGround [THBound b]
      RecursiveVar  -> generaliseVar v <&> \m -> TyGround [THMuBound m]
      SubVar w    -> if testBit l w then pure tyTop else readBounds (setBit l w) (setBit 0 w , [])
      SubTy ty    -> pure ty
    pure $ mergeTypeList pos (TyGround grounds : subs ++ varBounds)
  in readBounds loops . partitionType

--reconstructType :: forall s. MV.MVector s BiSub -> V.Vector VarSub -> Type -> TCEnv s Type
--reconstructType bis' varSubs ty = let
--  readBounds :: (Bool , BitSet , Type) -> TCEnv s (TypeF (Bool , BitSet , Type))
--  readBounds (pos , loops , seedTy) = let
--    (vs , gs) = partitionType seedTy
--    readVar v = MV.read bis' v <&> if pos then _pSub else _mSub
--    negArrows = mapTHeads $ \case
--      THTyCon (THArrow ars ret) -> THTyCon (THArrow ((\(p,l,t) -> (not p,l,t)) <$> ars) ret)
--      x -> x
--    in do
--    varBounds <- bitSet2IntList (vs .&. complement loops) `forM` readVar
--    subs <- bitSet2IntList vs `forM` \v -> case varSubs V.! v of
--      DeleteVar  -> pure tyBot
--      GeneraliseVar -> generaliseVar v <&> \b -> TyGround [THBound b]
--      RecursiveVar  -> generaliseVar v <&> \m -> TyGround [THMuBound m]
--      SubVar w    -> readVar w
--      SubTy ty    -> pure ty
--    let r = mergeTypeList pos (TyGround gs : subs ++ varBounds)
--        loops2 = loops .|. vs
--    partitionType r & \(rvs , rgs) -> if rvs .&. complement loops2 /= 0
--      then readBounds (pos , loops2 , (TyVars (rvs .&. complement loops2) rgs))
--      else pure $ negArrows $ (pos , loops2 ,) <$> project r -- TODO we should only recurse the raw tgrounds..
--  in anaM readBounds (True , 0 , ty) -- track strictly positive tvar wraps?
