{-# Language TemplateHaskell #-}
-- Biunfication records constraints , generalisation makes sense of them
module Generalise (generalise,) where
import Control.Lens
import CoreSyn
import CoreUtils
import PrettyCore ( number2CapLetter, prettyTyRaw )
import TCState
import qualified Data.Vector.Mutable as MV
import qualified Data.Text as T -- ( intercalate )
import qualified Data.Vector as V
import qualified Data.List
import Data.Functor.Foldable
debug_gen = False || global_debug

-- TODO audit whether the ad-hoc handling of THBI instantiations works:
-- * if type-merges of THBound involved
-- * higher rank polymorphism (stacked THBi)

indexed :: Traversable f => f a -> f (Int , a)
indexed f = traverse (\t -> get >>= \i -> modify (1+) $> (i , t)) f `evalState` 0

-- Simplification removes (or unifies with another type) as many tvars as possible
-- Generalisation allows polymorphic types to be instantiated with fresh tvars on each use: promote tvar to Π-bound
-- TVars and let-bindings:
-- 1. Escaped : tvars belong to outer let-nests, don't generalise (leave the raw tvar)
-- 2. Leaked  : local vars biunified with escaped vars (generalise and merge with raw tvar)
--   * necessary within let-binds to constrain free variables. considered dead outside the let-bind
-- 3. Dead    : formerly leaked vars once their scope expires.
--   * overconstrained since were biunified with instantiations of their let-binding
--   (while inferring their let-block, they leaked out by biunifying with an escaped var)
--
-- Escaped vars examples:
-- * f1 x = let y z = z in y   -- nothing can go wrong
-- * f2 x = let y   = x in y   -- if x generalised at y => f2 : a -> b (Wrong)
-- * f3 x = let y y = x y in y -- same problem
-- Note. because of escaped vars, a let-bindings type may contain raw tvars.
-- Later (eg. for codegen) need to 're'generalise to sub out free/escaped vars once they're resolved

-- Simplifications (performed just before commiting to generalising a tvar):
-- eg. foldr : (A -> (C & B) -> B) -> C -> μx.[Cons : {A , x} | Nil : {}] -> (B & C)
-- =>  foldr : (A -> B       -> B) -> B -> μx.[Cons : {A , x} | Nil : {}] -> B
--  * remove polar variables `a&int -> int => int->int` ; `int -> a => int -> bot`
--  * unify inseparable vars (polar co-occurence `a&b -> a|b` and indistinguishables `a -> b -> a|b`)
--  * unify variables that have the same upper and lower bound (a<:t and t<:a) `a&int -> a|int`
--  * tighten (roll) recursive types
--  * TODO: Type function subtyping: if A <: F A and F B <: B then A <: B

-- Generalisation is a 2 pass process
-- 1 Preparation & Analysis:
--   * read TVar bounds from Bisubs
--   * detect whether tvar cycles are guarded by TyCon (loops and recVars BitSets)
--   * save TVar co-occurences
--   * Co-occurence analysis: attempt to remove or unify tvars
-- 2. Finalise: Remove, unify or generalise (with possible mu binder) TVars based on co-occurence analysis

data VarSub = Remove | Escaped | Generalise | Recursive | Leaked | SubVar Int | SubTy Type deriving Show

type Cooc s = MV.MVector s ([Type] , [Type])
data AnalyseState s = AnalyseState { _anaBis :: MV.MVector s BiSub , _recs :: BitSet , _instVars :: Int , _coocs :: Cooc s }; makeLenses ''AnalyseState
type AnaEnv s = StateT (AnalyseState s) (ST s)

data GState s = GState { _quants :: Int , _genMap :: MV.MVector s Int }; makeLenses ''GState
type GEnv s = StateT (GState s) (ST s)

generalise ∷ BitSet -> Either IName Type -> TCEnv s Type
generalise escapees rawType = do
  when debug_gen (traceM $ "Gen: " <> show rawType)
  coocLen <- use bis <&> MV.length
  bis' <- use bis
  bl   <- use blen
  (analysedType , recursives , occurs) <- lift $ do -- re-use same ST state thread to avoid copying bisubs
    coocVStart <- MV.replicate coocLen ([],[])
    (ty , (AnalyseState _bis recs _instVs coocV)) <-
      -- merge with recTVar in case of direct recursion `r = { next = r } : µx.{next : x}`
      runStateT (analyseType ((TyVar ||| identity) rawType) True 0 0) (AnalyseState bis' 0 bl coocVStart)
    occurs <- V.unsafeFreeze coocV
    pure (ty , recs , occurs)
  nVars  <- use blen
  leaks  <- use leakedVars
  let tvarSubs = judgeVars nVars escapees leaks recursives occurs
      done     = forgetRoll . cata rollType $ runST $ do
        genMap  <- MV.replicate 100 (complement 0) -- TODO
        (t , s) <- runStateT (cata (doGen tvarSubs recursives) analysedType True) (GState 0 genMap)
        pure $ if s._quants == 0 then t else TyGround [THBi s._quants t]

  (done <$) $ when debug_gen $ do
    let showTys t        = T.intercalate " ; " (prettyTyRaw <$> t)
     in V.take nVars occurs `iforM_` \i (p,m) -> traceM (show i <> ": +[" <> showTys p <> "] -[" <> showTys m <> "]")
    traceM $ "analysed: " <> prettyTyRaw analysedType
    traceM $ "escapees: " <> show (bitSet2IntList escapees)
    traceM $ "leaked:   " <> show (bitSet2IntList leaks)
    traceM $ "recVars:  " <> show (bitSet2IntList recursives)
    traceM   "tvarSubs: " *> V.imapM_ (\i f -> traceM $ show i <> " => " <> show f) tvarSubs
    traceM $ "done: "     <> prettyTyRaw done

-- co-occurence with v in TList1 TList2: find a tvar or a type that always cooccurs with v
-- hoping to unify v with its co-occurence (straight up remove it if unifies with a var)
-- opposite co-occurence: v + T always occur together at +v,-v ⇒ drop v (unify with T)
-- polar co-occurence:    v + w always occur together at +v,+w or at -v,-w ⇒ unify v with w
-- ? unifying recursive and non-recursive vars (does the non-rec var need to be covariant ?)
judgeVars :: Int -> BitSet -> BitSet -> BitSet -> V.Vector ([Type] , [Type]) -> V.Vector VarSub
judgeVars nVars escapees leaks recursives coocs = V.constructN nVars $ \prevSubs -> let
  collectCoocVs = \case { [] -> 0 ; x : xs -> foldr (.&.) x xs }
  v = V.length prevSubs -- next var to analyse
  vIsRec = recursives `testBit` v
  (pOccs , mOccs) = coocs V.! v
  prevTVs = setNBits v -- sub in solved vars rather than redoing cooccurence analysis on them
  subPrevVars ∷ Bool -> Type -> Type
  subPrevVars pos ty = let
    (tvars , rest) = partitionType ty
    subVar w = let self = TyVars (setBit 0 w) [] in if w >= v then self else case prevSubs V.! w of
      Remove   -> TyGround []
      SubTy t  -> t
      SubVar x -> subVar x
      _        -> self -- Escaped Leaked Recursive Generalise
    in mergeTypeList pos $ [TyVars (complement prevTVs .&. tvars) [] , TyGround rest]
                    ++ (subVar <$> bitSet2IntList (prevTVs .&. tvars))
  ((pVars , pTs) , (mVars , mTs)) = ( unzip $ partitionType . subPrevVars True  <$> pOccs
                                    , unzip $ partitionType . subPrevVars False <$> mOccs)
  (coocPVs , coocMVs) = (collectCoocVs pVars , collectCoocVs mVars)
  generalise = if leaks `testBit` v then Leaked else if vIsRec then Recursive else Generalise

  in if -- Simplify: Try to justify Remove next Sub else fallback to Generalise
-- | v >= tVars -> did_ $ if recursives `testBit` v then Recursive else Generalise -- Instantiated vars
  | escapees `testBit` v -> Escaped -- belongs to a parent of this let-binding
  | not vIsRec && (null pOccs || null mOccs) -> if leaks `testBit` v then Escaped else Remove --'polar' var
  | otherwise -> let
    recMask = if vIsRec then recursives else complement recursives
    polarCooc ∷ Bool -> Int -> VarSub = \pos w -> let -- +: for ws in +v, look for coocs in +v,+w
      wCoocs = coocs V.! w
      wTypes = unzip $ partitionType . subPrevVars pos <$> (if pos then fst wCoocs else snd wCoocs)
      cooc w (vs , _vTs) (ws , _wTs) = if (collectCoocVs (vs ++ ws) `clearBit` v) /= 0 then SubVar w else generalise
      in {-d_ (v , w , pos) $-} if (null (fst wCoocs) || null (snd wCoocs))
      then generalise -- don't merge with a polar (or recursive variable)
      else cooc w (if pos then (pVars , pTs) else (mVars , mTs)) wTypes

    -- search ws found in v+ (or v-) note. we already attempted w < v , but may still be matches in the other var
    polarCoocs pos vCoocs = polarCooc pos <$> bitSet2IntList (vCoocs `clearBit` v)

    -- in v+v- if non-recursive v coocs with w then it always does, so "unify v with w" means "remove v"
    -- but in v+w+ or v-w- no shortcuts: "unify v with w" means "replace occurs of v with w"
    -- avoid unifying rec and non-rec vars (recMask .&.)
    vPvM = case bitSet2IntList $ (recMask .&. collectCoocVs (pVars ++ mVars)) `clearBit` v of
      -- Cannot generally shortcut to Remove; eg: v subvar w then remove w because w cooc x; wrong if v doesn't cooc x
      w : _ -> if True || vIsRec then SubVar w else Remove
      _     -> generalise

    -- Aggressively merge recursive vars even if only partial co-occurence
    vPvMRec = let partialRecCoocs = complement prevTVs .&. recMask .&. foldr (.|.) 0 (pVars ++ mVars) `clearBit` v
      in if vIsRec then maybe generalise SubVar (head (bitSet2IntList partialRecCoocs)) else generalise

    -- recmask to disallow merge x & A in (x & A) -> (µx.[Cons {%i32 , x}] & A)
    vPwP = polarCoocs True  ({-recMask .&.-} coocPVs) ∷ [VarSub]
    vMwM = polarCoocs False ({-recMask .&.-} coocMVs) ∷ [VarSub]
    -- look for some T present at all v+v- (since this is expensive and rarer try it last) `A & %i32 -> A & %i32`
    -- TODO fix this ; eg. THExt 1 and THPrim (PrimInt 32) are the same but fail here
    vTs = let allCoocs = concat (pTs ++ mTs) in maybe generalise (\t -> SubTy (TyGround [t]))
      $ head =<< head (filter ((== length pTs + length mTs) . length) (group {-$ sort-} allCoocs))
      -- need to sort since group only joins adjacent elements (but that requires Ord on Types)
      -- TODO tycon Intersects eg. { a : t , b : _ } and { a : T } have a co-occurence { a : T }
--  intersectCooc ∷ [TyHead] -> [TyHead] -> [TyHead] = \t intersects -> let -- valid cooc intersections
--    intersectTH th intersect

    -- use foldl' to stop once we've found a reason to either Remove or Sub the tvar
    bestSub ok next = case ok of { Remove -> ok ;  SubTy _ -> ok ; SubVar _ -> ok ; _ko -> next }
    in foldl' bestSub (vPvM `bestSub` vPvMRec) (vPwP ++ vMwM) `bestSub` vTs

-- tighten μ-types
-- This may need to know the polarity, for top/bot and to rm negative recursion
type Roller = [THead (Maybe Type)] -- x to μx. binder [TypeF] typeconstructor wrappers
data TypeRoll
 = NoRoll { forgetRoll :: Type }
 | BuildRoll { forgetRoll :: Type , muR :: Int , roller :: Roller }
 | Rolling   { forgetRoll :: Type , muR :: Int , roller :: Roller , resetRoll :: Roller }
 deriving Show
rollType :: TypeF TypeRoll -> TypeRoll
rollType this = let
  -- Aggregate TypeRolls from each sub-branch. Maybe building | rolling μs out of two branches
  aggregateBranches :: BitSet -> ([Int] , [THead TypeRoll]) -> TypeRoll
  aggregateBranches vs (ms , [th]) = let -- TODO need to handle type merges
    this = let tt = [forgetRoll <$> th] in if vs == 0 then TyGround tt else TyVars vs tt
    noop = case ms of
      []  -> NoRoll this
      [m] -> NoRoll (TyGround [THMu m this])
      _   -> _
    ith = Generalise.indexed th
    -- if. μ-bound in hole start μ-build
    -- if. μ-build in a hole => if μ-binder: stop build ||| continue build
    -- if. μ-roll in hole check if roll ok: either roll ||| test more layers
    in case find ((\case { BuildRoll{}->True ; _->False }) . snd) ith of -- TODO this only looks at the fst
      Just (i , BuildRoll _ m rollFn) -> let -- rolled = (Nothing <$ th) : rollFn
        rolled = ((\(j,t) -> if i == j then Nothing else Just (forgetRoll t)) <$> ith) : rollFn
        r = reverse rolled
        in if m `elem` ms then Rolling (TyGround [THMu m this]) m r r else BuildRoll this m rolled
      _Nothing -> case find ((\case { Rolling{} -> True ; _ -> False }) . snd) ith of
        Just (i , Rolling ty m reset (r : nextRolls)) -> let
          layer = (\(j,t) -> if i == j then Nothing else Just (forgetRoll t)) <$> ith
          in if {-d_ (layer , r) $-} layer /= r then NoRoll this else Rolling ty m reset (nextRolls <|> reset)
        _Nothing -> noop
  aggregateBranches vs ([], xs) = NoRoll $ mkTy vs (fmap forgetRoll <$> xs)
  aggregateBranches vs (m , []) = case m of
    [m] -> BuildRoll (mkTy vs [THMuBound m]) m []
    _   -> NoRoll $ mkTy vs []
  aggregateBranches v (m , xs) = trace ("μ-type merge: " <> show m <> " : " <> show xs :: Text)
    (aggregateBranches v ([] , xs))
  mkTy vs t = if vs == 0 then TyGround t else TyVars vs t
  partitionMus g = let (ms , gs) = Data.List.partition (\case {THMuBound{} -> True ; _ -> False}) g
    in (ms <&> (\(THMuBound m) -> m) , gs)
  in case this of
  TyVarsF vs g -> aggregateBranches vs (partitionMus g)
  TyGroundF g  -> aggregateBranches 0 (partitionMus g)
  TyVarF    v  -> NoRoll $ TyVar v
  _ -> NoRoll (embed $ fmap forgetRoll this)

deriving instance Show (THead (Maybe Type))
deriving instance Show (TyCon TypeRoll)
deriving instance Show (TyCon (Maybe Type))
deriving instance Show (THead TypeRoll)

-- Simplify + generalise TVars and add pi-binders
doGen :: V.Vector VarSub -> BitSet -> TypeF (Bool -> GEnv s Type) -> Bool -> GEnv s Type
doGen tvarSubs recs rawType pos = let
  generaliseVar :: Int -> GEnv s Int
  generaliseVar v = use genMap >>= \mp -> MV.read mp v >>= \perm ->
    if perm /= complement 0 then pure perm else do -- A..Z names for generalised typevars
      q <- quants <<%= (1+)
      when debug_gen (traceM $ show v <> " => ∀" <> toS (number2CapLetter q))
      q <$ MV.write mp v q

  genVar :: Int -> GEnv s Type
  genVar v = if v >= V.length tvarSubs
    then generaliseVar v <&> \q -> TyGround [if testBit recs v then THMuBound q else THBound q] 
    else case tvarSubs V.! v of
    Escaped    -> pure (TyVar v)
    Remove     -> pure (TyGround []) -- pure $ if leaks `testBit` v then TyVar v else TyGround []
    Leaked     -> generaliseVar v <&> \q -> TyVars (setBit 0 v) [THBound q]
    Recursive  -> generaliseVar v <&> \q -> TyGround [THMuBound q]
    Generalise -> generaliseVar v <&> \q -> TyGround [THBound q]
    SubVar i   -> genVar i
    SubTy t    -> cata (doGen tvarSubs recs) t pos -- TODO can contain rec vars accross type substitutions?

  go :: BitSet -> [THead (Bool -> GEnv s Type)] -> GEnv s Type
  go vars g = let
    varSubs = bitSet2IntList vars `forM` genVar
    grounds :: [THead (Bool -> GEnv s Type)] -> GEnv s GroundType
    grounds g = g `forM` \case
      (THTyCon (THArrow ars r)) -> fmap THTyCon $ THArrow -- THArrow is the only tycon with contravariant subtrees
        <$> traverse (\arg -> arg (not pos)) ars <*> r pos
      x -> traverse (\x -> x pos) x
    in (\grounds vs -> mergeTypeList pos (TyGround grounds : vs)) <$> grounds g <*> varSubs

  in case rawType of
    TyGroundF gs  -> go 0 gs
    TyVarF v      -> genVar v
    TyVarsF vs gs -> go vs gs
    x             -> embed <$> traverse (\f -> f pos) x

--------------------
-- Analysis Phase --
--------------------
-- TODO THBound -> new THBound map (or do we never merge THBounds ?)
-- Subs in tyvar with bisub results and builds cooc vector
type Acc s = Bool -> BitSet -> BitSet -> AnaEnv s Type
analyseType :: Type -> Acc s
analyseType = let
  registerOccurs ∷ Bool -> Type -> AnaEnv s Type
  registerOccurs pos ty = use coocs >>= \cooc -> partitionType ty & \(vset , other) ->
    ty <$ bitSet2IntList vset `forM` \i ->
      MV.modify cooc (over (if pos then _1 else _2) (TyVars vset other :)) i

  subVar pos loops guarded v = if
    | testBit loops v   -> pure (TyVars loops []) -- unguarded var loop
    | testBit guarded v -> TyVars (0 `setBit` v) [] <$ (recs %= (`setBit` v))
    | otherwise -> use anaBis >>= \b -> use instVars >>= \iv -> if v >= iv then pure $ TyVar v -- THBound vars spawned in later
      else MV.read b v >>= \(BiSub pty mty) -> let -- not atm a TVar cycle
      loops' = setBit loops v
      ty = if pos then pty else mty
      in if nullType ty then pure (TyVars loops' []) else mergeTVar v <$> analyseType ty pos loops' guarded

  go :: [THead (Acc s)] -> BitSet -> Acc s
  go g vars pos loops guarded = let
    varSubs = bitSet2IntList vars `forM` subVar pos loops guarded
    mkT t = TyGround [t]
    grounds :: [THead (Acc s)] -> AnaEnv s [Type] -- GroundType
    grounds g = let loops' = 0 ; guarded' = guarded .|. loops .|. vars in g `forM` \case
      tycon@(THTyCon t) -> fmap mkT $ case t of -- update loops and guarded for tycons
     -- THArrow is the only tycon with contravariant subtrees
        THArrow ars r -> fmap THTyCon $ THArrow
          <$> traverse (\arg -> registerOccurs (not pos) =<< arg (not pos) loops' guarded') ars <*> (registerOccurs pos =<< r pos loops' guarded')
        _ -> traverse (\x -> registerOccurs pos =<< x pos loops' guarded') tycon

      -- THBounds cannot occur together with tvars, else would have been instantiated already
      THBound b   -> use instVars >>= \vn -> {-checkRec guarded (vn + b) *>-}subVar pos loops guarded (vn + b)
      THMuBound m -> use instVars >>= \vn -> {-(recs %= (`setBit` (vn + m))) *>-} subVar pos loops guarded (vn + m)
      THBi _b ty  -> {-(instVars <<%= (b+)) *>-} ty pos loops guarded -- TODO stacked THBis?
      THMu m ty -> use instVars >>= \vn ->
        (recs %= (`setBit` (vn + m))) *> ty pos loops guarded <&> mergeTVar (vn + m)
      x -> mkT <$> traverse (\x -> x pos loops guarded) x
    in (\grounds vs -> mergeTypeList pos (grounds ++ vs)) <$> grounds g <*> varSubs

  in cata $ \t pos loops guarded -> case t of
    TyGroundF g  -> go g 0  pos loops guarded
    TyVarsF vs g -> go g vs pos loops guarded
    TyVarF v     -> subVar pos loops guarded v
    x -> embed <$> traverse (\x -> x pos loops guarded) x
