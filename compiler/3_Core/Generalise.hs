-- Biunfication records constraints , generalisation makes sense of them
module Generalise (generalise) where
import CoreSyn
import CoreUtils
import PrettyCore
import TCState
import BiUnify (instantiate)
import Control.Lens
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector as V
import qualified Data.Text as T

-- Generalisation allows polymorphic types to be instantiated with fresh tvars on each use.
-- Only generalise local tvars; if a Gen'd var escapes into enclosing scope it could be instantiated to anything there
-- escapedVars : BitSet indicates which tvars escape and should be left alone
-- thus most let-bindings have to be generalised twice
--  1. if locally used more than once they need to be instantiatable (else can skip and inline it)
--  2. finally fully generalise it once its freevars have been generalised at enclosing scope
-- * f1 x = let y z = z in y   -- nothing can go wrong
-- * f2 x = let y   = x in y   -- if x generalised at y => f2 : a -> b
-- * f3 x = let y y = x y in y -- similar

-- The idea is to make sure that escaped tvars never refer to ones enclosed deeper
-- instantiate = replace tvars at or above lvl with fresh vars at lvl
-- constraining: while types / tvars came from deeper let-nest, make new tvars at this lvl

-- Simplifications:
--  * ? A -> A & Int =? Int -> Int
--  * remove polar variables `a&int -> int` => int->int ; `int -> a` => `int -> bot`
--  * unify inseparable variables (polar co-occurence `a&b -> a|b` and indistinguishables `a->b->a|b`)
--  * unify variables that contain the same upper and lower bound (a<:t and t<:a) `a&int->a|int`
--  * tighten recursive types

-- eg. foldr : (A → (C & B) → B) → C → μx.[Cons : {A , x} | Nil : {}] → (B & C)
-- =>  foldr : (A → B → B) → B → μx.[Cons : {A , x} | Nil : {}] → B

-- Generalisation is a 2 pass process
-- 1 Preparation & Analysis:
--   * read TVar bounds from Bisubs
--   * detect whether tvar cycles are guarded by TyCon (loops and recVars BitSets)
--   * save TVar co-occurences
--   * Co-occurence analysis: with each tvar either
--     - generalise (including recursive tvars)
--     - unify with some type or typevar
-- 2. Finalise: Remove or generalise (maybe with mu binder) all TVars depending on results of co-occurence analysis
generalise :: BitSet -> IName -> TCEnv s Type
generalise escapees recTVar = let
  showTys t        = T.intercalate " , " (prettyTyRaw <$> t)
  traceCoocs occLen coocs = [0..occLen -1] `forM_` \i -> MV.read coocs i >>= \(p,m) ->
    traceM (show i <> ": + [" <> showTys p <> " ]; - [" <> showTys m <> "]")
  in do
  when global_debug (traceM $ "Gen: " <> show recTVar)
  (quants .= 0) *> (quantsRec .= 0)

  bs <- use bis
  let coocLen = MV.length bs + 5 -- + let-bound instantiatables TODO
  (biEqui .=)   =<< MV.replicate coocLen (complement 0)
  (coOccurs .=) =<< MV.replicate coocLen ([],[])
  recVars .= 0

  analysed   <- substTypeVar True recTVar emptyBitSet emptyBitSet
  recursives <- use recVars
  occurs     <- use coOccurs
  occLen     <- use blen
  when global_debug (traceCoocs occLen occurs)
  -- patch in self if it was recursive
  tvarSubs <- coocVars occLen escapees recursives <$> V.unsafeFreeze occurs

  when global_debug $ do
    traceM $ "analysed: "   <> prettyTyRaw analysed
    traceM $ "escapees: "   <> show (bitSet2IntList escapees)
    traceM $ "recVars:  "   <> show (bitSet2IntList recursives)
    traceM   "tvarSubs: "   *> V.imapM_ (\i f -> traceM $ show i <> " => " <> show f) tvarSubs

  done <- subGen tvarSubs analysed
  when global_debug $ traceM $ "done: " <> (prettyTyRaw done)
  pure done

-- co-occurence with v in TList1 TList2: find a tvar or a type that always cooccurs with v
-- hoping to unify v with its co-occurence (straight up remove it if unifies with a var)
-- * unifying recursive and non-recursive vars is only admissible if the non-rec var is covariant
-- opposite co-occurence: v + T always occur together at +v,-v => drop v (unify with T)
-- polar co-occurence:    v + w always occur together at +v,+w or at -v,-w => drop v (unify with w)
-- ! Sub should never sub in a tvar
data VarSub = Remove | Escaped | Generalise | Recursive | SubVar Int | SubTy Type deriving Show
--coocVars occLen escapees recursives coocs = V.constructN occLen $ \prevSubs -> let
coocVars :: Int -> BitSet -> BitSet -> V.Vector ([Type] , [Type]) -> V.Vector VarSub
coocVars occLen escapees recursives coocs = V.constructN occLen $ \prevSubs -> let
  collectCoocVs [] = 0
  collectCoocVs (x:xs) = foldr (.&.) x xs
  v = V.length prevSubs -- next var to analyse
  prevTVs = setNBits v  -- sub in solved vars rather than redoing cooccurence analysis on them
  (pOccs , mOccs) = (coocs V.! v)
  subPrevVars :: Type -> Type
  subPrevVars ty = let
    (tvars , rest) = partitionType ty
    subVar w = let self = TyVars (setBit 0 w) [] in if w >= v then self else case prevSubs V.! w of
      Remove     -> TyGround []
      Escaped    -> self
      Generalise -> self
      SubTy t    -> t
      SubVar x   -> subVar x -- it is possible x is < v and should be subbed
--  nextTVars = THVars (complement prevTVs .&. allTVars)
--  in partitionTVars ([[nextTVars]] ++ rest ++ (subVar <$> bitSet2IntList (prevTVs .&. allTVars)))
    in mergeTypeList $ [TyVars (complement prevTVs .&. tvars) [] , TyGround rest] ++ (subVar <$> bitSet2IntList (prevTVs .&. tvars))
  ((pVars , pTs) , (mVars , mTs)) = ( unzip $ partitionType . subPrevVars <$> pOccs
                                    , unzip $ partitionType . subPrevVars <$> mOccs)
  (coocPVs , coocMVs) = (collectCoocVs pVars , collectCoocVs mVars)

  cooc (vs , vTs) (ws , wTs) = let
    coocVars = collectCoocVs (vs ++ ws) `clearBit` v
    in if coocVars /= 0
       then SubVar (fromJust (head (bitSet2IntList coocVars)))
       else coocType vTs wTs

  coocType pTs mTs = case Nothing of --case typeIntersection (pTs ++ mTs) of -- find some ty present everywhere to unify with
    Just t  -> SubTy t
    Nothing -> Generalise
  polar = null pOccs || null mOccs -- Recursive typevars must be polar (ie. covariant)
  in if -- Max simplification involves trying hard to avoid Generalise by justifying Remove, or failing that, Sub
  | escapees `testBit` v -> Escaped -- belongs to deeper let nest
  | polar -> if recursives `testBit` v then Recursive else Remove
  | otherwise -> let
    polarCooc :: Bool -> Int -> VarSub -- eg. + case: for all w in +v, look for coocs in +v,+w
    polarCooc pos w = let wCoocs = coocs V.! w ; wCooc = if pos then fst wCoocs else snd wCoocs in {-d_ (v , w , pos) $-} 
      if null (fst wCoocs) || null (snd wCoocs) then Generalise -- don't merge with a polar (or recursive variable)
      else -- let (wVars , wTs) = unzip $ partitionType <$> ((if pos then fst else snd) wCoocs)
      cooc (if pos then (pVars , pTs) else (mVars , mTs)) (unzip $ partitionType . subPrevVars <$> wCooc)
    -- in v+v- when unifying v with w we can directly remove v because it always co-occurs with w
    vPvM = if collectCoocVs (pVars ++ mVars) `clearBit` v /= 0 then Remove else coocType pTs mTs

    vPwP , vMwM :: [VarSub] -- Note. we already attempted to unify w<v with v, so only try w>v
    vPwP = polarCooc True  <$> bitSet2IntList ((complement prevTVs .&. coocPVs) `clearBit` v)
    vMwM = polarCooc False <$> bitSet2IntList ((complement prevTVs .&. coocMVs) `clearBit` v)
    -- use foldl' to stop once we've found a reason to either Remove or Sub the tvar
    bestSub ok next = case ok of { Remove -> ok ; (SubTy t) -> ok ; (SubVar v) -> ok ; ko -> next }
    in foldl' bestSub vPvM (vPwP ++ vMwM) -- if none of this found anything the tvar will Generalise

-- Final step; eliminate all TVars
-- * either sub in THBound | unify with co-occurences (possibly [])
subGen :: V.Vector VarSub -> Type -> TCEnv s Type
subGen tvarSubs raw = use bis >>= \b -> use biEqui >>= \biEqui' -> use coOccurs >>= \coocs -> let
  generaliseRecVar v = MV.read biEqui' v >>= \perm -> if perm /= complement 0 then pure perm else do
      m <- quantsRec <<%= (+1)
      when global_debug (traceM $ show v <> " =>µ " <> toS (number2xyz m))
      m <$ MV.write biEqui' v m
  generaliseVar v = MV.read biEqui' v >>= \perm -> if perm /= complement 0 then pure perm else do
      q <- quants <<%= (+1)
      when global_debug (traceM $ show v <> " =>∀ " <> toS (number2CapLetter q))
      q <$ MV.write biEqui' v q

  doVar pos v = case tvarSubs V.! v of
    Remove     -> pure (TyGround [])
    Escaped    -> pure (TyVars (0 `setBit` v) [])
    Generalise -> generaliseVar v    <&> \q -> TyGround [THBound q]
    Recursive  -> generaliseRecVar v <&> \m -> TyGround [THMuBound m]
    SubVar i   -> doVar pos i
    SubTy t    -> goType pos t -- pure t
  goType pos = \case
--  TyVars vs g -> (\a b -> mergeTypeList (a ++ b)) <$> (doVar pos `mapM` bitSet2IntList vs) <*> (finaliseTyHead pos `mapM` g)
--  Do the non-typevars first so they get naming priority for generalisation `(A -> B) & B` rather than `(B -> A) & A`
    TyVars vs g -> (\a b -> mergeTypeList (a ++ b)) <$> (finaliseTyHead pos `mapM` g) <*> (doVar pos `mapM` bitSet2IntList vs)
    TyVar v    -> doVar pos v
    TyGround g -> mergeTypeList <$> finaliseTyHead pos `mapM` g
  goGuarded pos = fmap (tyLatticeEmpty pos) . goType pos --fmap (tyLatticeEmpty pos) . goType pos 
  finaliseTyHead pos = \case
--  THVars v  -> foldr mergeTypes [] <$> (doVar pos `mapM` bitSet2IntList v)
--  THVar v   -> doVar pos v
    x -> (\x -> TyGround [x]) <$> case x of
      THBi b m ty -> THBi b m <$> goType pos ty
      THTyCon t   -> THTyCon  <$> case t of
        THArrow ars r -> THArrow   <$> traverse (goGuarded (not pos)) ars <*> goGuarded pos r
        THProduct   r -> THProduct <$> traverse (goGuarded       pos) r
        THSumTy     r -> THSumTy   <$> traverse (goGuarded       pos) r
        THTuple     r -> THTuple   <$> traverse (goGuarded       pos) r
      x -> pure x
  in goGuarded True raw >>= \done -> use quants >>= \q -> use quantsRec <&> \m ->
    if m + q > 0 then TyGround [THBi q m done] else done

--------------------
-- Analysis Phase --
--------------------
-- Read typevars from Bisubs, collect co-occurences and identify recursive types
-- non-escaped typevars are possibly safe to cache their substitution to (=<< updateVar)
substTypeVar :: Bool -> Int -> BitSet -> BitSet -> TCEnv s Type
substTypeVar pos v loops guarded = use bis >>= \b -> if
  | testBit loops v   -> pure (TyVars loops []) -- unguarded var loop
  | testBit guarded v -> TyVars (0 `setBit` v) [] <$ (recVars %= (`setBit` v))
  | otherwise -> MV.read b v >>= \(BiSub pty mty) -> let -- not atm a TVar cycle
    loops'    = setBit loops v
    ty = if pos then pty else mty
    in if nullType ty
       then pure $ TyVars loops' []
       else substTypeMerge pos loops' guarded ty
--  in case (if pos then pty else mty) of
--    [] -> pure [THVars loops']
--    ty -> substTypeMerge pos loops' guarded ty

-- typevars need to know what they co-occur with, for simplification purposes
registerOccurs :: Bool -> Type -> TCEnv s Type
registerOccurs pos ty = use coOccurs >>= \cooc -> let
  (vset , other)    = partitionType ty -- partition ((== KVars) . kindOf) $ ty
--vset              = foldr (.|.) 0 $ (\(THVars v) -> v) <$> vars
--mkTy vset i other = THVars vset : other -- leave the var itself in the vset
  in ty <$ bitSet2IntList vset `forM` \i ->
    MV.modify cooc (over (if pos then _1 else _2) (TyVars vset other :)) i
--  MV.modify cooc (over (if pos then _1 else _2) (mkTy vset i other :)) i

substTypeMerge :: Bool -> Integer -> Integer -> Type -> TCEnv s Type
substTypeMerge pos loops guarded ty =  let
  (tvars , others) = partitionType ty -- partition (\case { THVars{}->True;THVar{}->True;_->False}) ty
--tvars = foldr (.|.) 0 (\case { THVars v -> v ; THVar i -> setBit 0 i } <$> tvarsRaw)
  guarded' = guarded .|. loops .|. tvars
  substTyHead = let
    substGuarded p t = substTypeMerge p 0 guarded' t >>= registerOccurs p
    in \case
    THTyCon t -> (\x -> TyGround [THTyCon x]) <$> case t of
      THArrow ars r -> THArrow   <$> traverse (substGuarded (not pos)) ars
                                 <*> substGuarded pos r
      THProduct   r -> THProduct <$> traverse (substGuarded pos) r
      THSumTy     r -> THSumTy   <$> traverse (substGuarded pos) r
      THTuple     r -> THTuple   <$> traverse (substGuarded pos) r
    t@THPrim{} -> pure $ TyGround [t]
    t@THExt{} ->  pure $ TyGround [t]
    t@THTop{} ->  pure $ TyGround [t]
    t@THBot{} ->  pure $ TyGround [t]
    THBi n m t  -> instantiate n m t >>= substGuarded pos -- a generalised let-bound function
--  t@THMu{}  -> pure [t]
    x -> error $ show x --pure [x]
  in do
    vs <- bitSet2IntList tvars `forM` \x -> mergeTVar x <$> substTypeVar pos x loops guarded
--    (THVars (setBit 0 x) :) <$> substTypeVar pos x loops guarded
    ts <- substTyHead `mapM` others
    pure (mergeTypeList (vs ++ ts))
--  pure (foldr mergeTypes [] (vs ++ ts))
