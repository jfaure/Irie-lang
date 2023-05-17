-- WIP Rewrite of Generalise
module Typer where
import Control.Lens
import CoreSyn
import CoreUtils
import PrettyCore (number2CapLetter , prettyTyRaw)
import TCState
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector as V
import Data.List (intersect)
debug_gen = False || global_debug

-- generalise: standard rule for polymorphism=
-- good :: forall a . IO (IORef (Maybe a))
-- bad  :: IO (forall a . IORef (Maybe a))
-- ⊥ = ∀α.
-- ⊤ = ∃α. But conversions depend on variance
-- ∃α.(List[α] -> Int)a => List[⊥]->Int (since all uses of α are contravariant) , but not List[⊤]->Int
-- iff expr has a type A mentioning tvar a, and a is only used in A, then it can be reused with different types substituted for a
-- if polymorphic type inferred inside a variable f, f must not mention the polymorphic variable else it escapes its scope

tyVars vs g = if vs == 0 then TyGround g else TyVars vs g

intersectTypes :: Type -> Type -> Type
intersectTypes a b = case (partitionType a , partitionType b) of
  ((v , g) , (w , f)) -> TyVars (v .&. w) (intersect f g)

type Cooc = (Maybe Type , Maybe Type) -- recursive
data VarSub = Recursive Type | SubVar Int | SubTy Type | DeleteVar | GeneraliseVar | EscapedVar deriving Show

generalise :: forall s. BitSet -> Either IName Type -> TCEnv s Type
generalise lvl0 rawType = let startType = ((\x -> TyVars (setBit 0 x) []) ||| identity) rawType
  in do
  recursives .= 0
  bl    <- use blen
  bis'  <- use bis
  coocV <- MV.replicate bl (Nothing , Nothing)
  rawT <- buildCoocs bis' coocV 0 True startType
  coocVF <- V.freeze coocV
  recs <- use recursives
  varSubs <- buildVarSubs bis' coocVF recs lvl0
  traceM (prettyTyRaw rawT)
  traceM $ "lvl0: " <> show (bitSet2IntList lvl0)
  traceM $ "recs: " <> show (bitSet2IntList recs)
  traceShowM (V.indexed varSubs)

  MV.replicate 100 (complement 0) >>= (genVec .=) -- TODO
  nquants .= 0
  done <- buildType lvl0 bis' varSubs 0 True startType
  use nquants <&> \case { 0 -> done ; n -> TyGround [THBi n done] }

buildVarSubs _bis' coocV recs lvl0 = let
  len = V.length coocV
  recursiveVar = pure GeneraliseVar
  in do
  varSubs <- MV.new len
  [0.. len - 1] `forM_` \v -> let cooc = coocV V.! v in traceM (show v <> " => " <> show cooc) *>
    MV.write varSubs v =<< case cooc of
      _ | testBit lvl0 v -> pure EscapedVar
      (Nothing , t) -> if testBit recs v then d_ t $ recursiveVar else pure DeleteVar -- polar variables
      (t , Nothing) -> if testBit recs v then d_ t $ recursiveVar else pure DeleteVar

      -- in v+v- if non-recursive v coocs with w then it always does, so "unify v with w" means "remove v"
      -- but in v+w+ or v-w- no shortcuts: "unify v with w" means "replace occurs of v with w"
      (Just x , Just y) -> let
        prevTVs = setNBits v :: Integer -- don't redo co-occurence on prev-vars
        cooc x y = case partitionType (intersectTypes x y) of
          (vs , _ts) | clearBit vs v /= 0 -> DeleteVar
          (_vs , ts) | (x:_) <- ts -> d_ x DeleteVar
          _t -> GeneraliseVar
        oppCooc t pol = partitionType t & \(ws , _) ->
          maybe GeneraliseVar (cooc t) . (if pol then fst else snd) . (coocV V.!) <$> bitSet2IntList (complement prevTVs .&. ws)
        bestSub ok next = case ok of { DeleteVar -> ok ; SubTy _ -> ok ; SubVar _ -> ok ; _ko -> next }
        in pure $ foldl' bestSub (cooc x y) (oppCooc y True ++ oppCooc x False)
  V.freeze varSubs

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
      MV.modify coocV (over (if pos then _1 else _2) (Just . maybe (TyVars ws gs) (intersectTypes (TyVars ws gs)))) w
    pure ret
  in go guards . partitionType

-- reconstruct type using inferred bounds and co-occurence analysis
buildType :: forall s. BitSet -> MV.MVector s BiSub -> V.Vector VarSub -> BitSet -> Bool -> Type -> TCEnv s Type
buildType lvl0 bis' varSubs loops pos = let
  b = buildType lvl0 bis' varSubs
  generaliseVar v = use genVec >>= \mp -> MV.read mp v >>= \perm -> if perm /= complement 0 then pure perm else do
    q <- nquants <<%= (1+)
    q <$ MV.write mp v q <* when debug_gen (traceM $ show v <> " => ∀" <> toS (number2CapLetter q))

  go loops (vs , gs) = do
    let l = loops .|. vs
    grounds <- gs `forM` \case
      THTyCon (THArrow ars ret) -> fmap THTyCon $ THArrow <$> (b l (not pos) `mapM` ars) <*> b l pos ret
      t -> b l pos `mapM` t
    varBounds <- bitSet2IntList (vs .&. complement loops) `forM` \v ->
      MV.read bis' v >>= \(BiSub p m) -> go l (partitionType $ if pos then p else m)
    -- The big question is which vars to drop / sub
    subs <- bitSet2IntList vs `forM` \v -> case varSubs V.! v of
      EscapedVar -> pure (tyVar v)
      GeneraliseVar -> -- if testBit lvl0 v {- escaped variables-} then pure (tyVar v) else
        generaliseVar v <&> \b -> TyGround [THBound b] -- pure $ tyVar v
      DeleteVar     -> pure $ tyBot
      Recursive _ -> _
      SubVar _    -> _
      SubTy _     -> _
    pure $ mergeTypeList pos (TyGround grounds : subs ++ varBounds)
  in go loops . partitionType
