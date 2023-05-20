module Typer (generalise) where
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
debug_gen = False || global_debug

type Cooc = (Maybe Type , Maybe Type)
data VarSub = Recursive Type | SubVar Int | SubTy Type | DeleteVar | GeneraliseVar | RecursiveVar | EscapedVar deriving (Show , Eq)

generalise :: forall s. BitSet -> Either IName Type -> TCEnv s Type
generalise lvl0 rawType = do
  let startType = (tyVar ||| identity) rawType
  recursives .= 0
  bl    <- use blen
  bis'  <- use bis
  coocV <- MV.replicate bl (Nothing , Nothing)
  rawT  <- buildCoocs bis' coocV 0 True startType
  recs    <- use recursives
  coocVF  <- V.unsafeFreeze coocV
  let varSubs = buildVarSubs bis' coocVF recs lvl0
  MV.replicate 8000 (complement 0) >>= (genVec .=) -- TODO HACK size
  nquants .= 0
  when False $ do
    traceM (prettyTyRaw rawT)
    --let recTypes = (\i -> (\(a , b) -> (i , fromMaybe _ (a <|> b))) (coocVF V.! i)) <$> bitSet2IntList recs
    --traceM $ "recTypes:\n" <> (unlines $ (\(i , t) -> show i <> ": " <> prettyTyRaw t) <$> recTypes)
    --rTs <- recTypes `forM` \(i , t) -> (i,) <$> buildType bis' varSubs 0 True t
    --traceM $ "rTs:\n" <> (unlines $ (\(i , t) -> show i <> ": " <> prettyTyRaw t) <$> rTs)
    traceM $ "lvl0: " <> show (bitSet2IntList lvl0)
    traceM $ "recs: " <> show (bitSet2IntList recs)
    traceM (unlines $ V.toList $ show <$> V.indexed coocVF)
    traceM (unlines $ V.toList $ show <$> V.indexed varSubs)

  done <- buildType bis' varSubs 0 True startType
--done <- reconstructType bis' varSubs startType
  let rolled = forgetRoll (cata rollType done)
  use nquants <&> \case { 0 -> rolled ; n -> TyGround [THBi n rolled] }

buildVarSubs _bis' coocV recs lvl0 = V.constructN (V.length coocV) $ \varSubs -> let
  v = V.length varSubs
  prevTVs = setNBits v :: Integer -- don't redo co-occurence on prev-vars
  in case coocV V.! v of
  _ | testBit lvl0 v -> EscapedVar
  -- in v+v- if non-recursive v coocs with w then it always does, so "unify v with w" means "remove v"
  -- but in v+w+ or v-w- no shortcuts: "unify v with w" means "replace occurs of v with w"
  (Just x , Just y) -> let
    genVar = if testBit recs v then RecursiveVar else GeneraliseVar
    cooc x y = partitionType (intersectTypes x y) & \(vs , ts) -> let
     xx = if clearBit (getTyVars x) v == 0 then getTyVars y else 0
     yy = if clearBit (getTyVars y) v == 0 then getTyVars x else 0
     canSub v = (varSubs V.! v) & \vs -> vs == GeneraliseVar || vs == RecursiveVar --nesting SubVars is too complicated
     subCandidates = filter canSub $ bitSet2IntList (clearBit ((vs .|. xx .|. yy) .&. prevTVs) v)
     r = case head subCandidates of
      Just w  -> SubVar w -- Don't sub for polar vars!
      Nothing -> if null ts then genVar {-GeneraliseVar-} else SubTy (TyGround ts)
     in r --trace (show v <> " (" <> prettyTyRaw x <> " <=> " <> prettyTyRaw y <> ")" <> show ts <> " => " <> show r) r
--  in cooc x y
--  TODO make this more efficient (scansum needs it)
    oppCooc t pol = partitionType t & \(ws , _) -> bitSet2IntList (complement prevTVs .&. ws)
      <&> maybe GeneraliseVar (cooc t) . (if pol then fst else snd) . (coocV V.!)
    bestSub ok next = case ok of { DeleteVar -> ok ; SubTy _ -> ok ; SubVar _ -> ok ; _ko -> next }
    in foldl' bestSub (cooc x y) (oppCooc y True ++ oppCooc x False)
  (polarP , polarN) -> let
    noMergeRec = 0 == prevTVs .&. recs .&. (fromMaybe 0 ((fst . partitionType) <$> (polarP <|> polarN)))
    in if testBit recs v && noMergeRec then RecursiveVar else DeleteVar

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
      t -> b l pos `mapM` t
    let ret = mergeTypeList pos (tyVars vs grounds : varBounds) -- Which vars can be dropped / generalised?
    partitionType ret & \(ws , gs) -> bitSet2IntList ws `forM_` \w ->
      (recursives %= (.|. (ws .&. guards))) *>
      MV.modify coocV (over (if pos then _1 else _2) (Just . maybe (TyVars ws gs) (unionTypes (TyVars ws gs)))) w
    pure ret
  in go guards . partitionType

generaliseVar :: Int -> TCEnv s Int
generaliseVar v = use genVec >>= \mp -> MV.read mp v >>= \perm -> if perm /= complement 0 then pure perm else do
  q <- nquants <<%= (1+)
  q <$ MV.write mp v q <* when debug_gen (traceM $ show v <> " => ∀" <> toS (number2CapLetter q))

-- reconstruct type using inferred bounds and co-occurence analysis
buildType :: forall s. MV.MVector s BiSub -> V.Vector VarSub -> BitSet -> Bool -> Type -> TCEnv s Type
buildType bis' varSubs loops pos = let
  readBounds :: BitSet -> (BitSet , GroundType) -> TCEnv s Type
  readBounds loops (vs , gs) = do
    let l = loops .|. vs
        b = buildType bis' varSubs
    grounds <- gs `forM` \case
      THTyCon (THArrow ars ret) -> fmap THTyCon $ THArrow <$> (b l (not pos) `mapM` ars) <*> b l pos ret
      t -> b l pos `mapM` t
    varBounds <- bitSet2IntList (vs .&. complement loops) `forM` \v ->
      MV.read bis' v >>= \(BiSub p m) -> readBounds l (partitionType $ if pos then p else m)
    -- The big question is which vars to drop / sub
    subs <- bitSet2IntList vs `forM` \v -> case varSubs V.! v of
      DeleteVar     -> pure tyBot
      EscapedVar -> pure (tyVar v)
      GeneraliseVar -> generaliseVar v <&> \b -> TyGround [THBound b]
      RecursiveVar  -> generaliseVar v <&> \m -> TyGround [THMuBound m]
      Recursive _ -> _
      SubVar w    -> if testBit l w then pure tyTop else readBounds (setBit l w) (setBit 0 w , [])
      SubTy ty    -> pure ty
    pure $ mergeTypeList pos (TyGround grounds : subs ++ varBounds)
  in readBounds loops . partitionType

-- TODO use this instead of buildType: Need to add escapedVars to loops somehow!
reconstructType :: forall s. MV.MVector s BiSub -> V.Vector VarSub -> Type -> TCEnv s Type
reconstructType bis' varSubs ty = let
  readBounds :: (Bool , BitSet , Type) -> TCEnv s (TypeF (Bool , BitSet , Type))
  readBounds (pos , loops , seedTy) = let
    (vs , gs) = partitionType seedTy
    readVar v = MV.read bis' v <&> if pos then _pSub else _mSub
    negArrows = mapTHeads $ \case
      THTyCon (THArrow ars ret) -> THTyCon (THArrow ((\(p,l,t) -> (not p,l,t)) <$> ars) ret)
      x -> x
    in do
    varBounds <- bitSet2IntList (vs .&. complement loops) `forM` readVar
    subs <- bitSet2IntList vs `forM` \v -> case varSubs V.! v of
      EscapedVar -> pure (tyVar v) -- TODO Don't keep re-subbing escaped vars!
      DeleteVar  -> pure tyBot
      GeneraliseVar -> generaliseVar v <&> \b -> TyGround [THBound b]
      RecursiveVar  -> generaliseVar v <&> \m -> TyGround [THMuBound m]
      Recursive _ -> _
      SubVar w    -> readVar w
      SubTy ty    -> pure ty
    let r = mergeTypeList pos (TyGround gs : subs ++ varBounds)
        loops2 = loops .|. vs
    partitionType r & \(rvs , rgs) -> if rvs .&. complement loops2 /= 0
      then readBounds (pos , loops2 , (TyVars (rvs .&. complement loops2) rgs))
      else pure $ negArrows $ (pos , loops2 ,) <$> project r
  in anaM readBounds (True , 0 , ty) -- track strictly positive tvar wraps?
