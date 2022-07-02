-- Biunfication records constraints , generalisation makes sense of them
module Generalise (generalise,) where
import CoreSyn
import CoreUtils
import PrettyCore
import TCState
import BiUnify (instantiate)
import Control.Lens
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector as V
import qualified Data.Text as T
--import qualified Data.IntMap as IM (mapAccum , elems)
import qualified BitSetMap as BSM (mapAccum , elems)

-- Generalisation allows polymorphic types to be instantiated with fresh tvars on each use.
-- This means some tvars are to be promoted to polymorphic vars
-- However simplification removes (or unifies with another type) as many tvars as possible
-- TVars and let-bindings:
-- 1. Escaped : tvars belong to outer let-nests, don't generalise (leave the raw tvar)
-- 2. Leaked  : local vars biunified with escaped vars (generalise and merge with raw tvar)
--   * necessary within let-binds to constrain free variables. considered dead outside the let-bind
-- 3. Dead    : formerly leaked vars once their scope expires. They are now overconstrained since were biunified with instantiations of their let-binding (they're present outside of their let binding due to at one point leaking through a constraint)
-- Escaped vars examples:
-- * f1 x = let y z = z in y   -- nothing can go wrong
-- * f2 x = let y   = x in y   -- if x generalised at y => f2 : a → b
-- * f3 x = let y y = x y in y -- similar
-- Note. because of escaped vars, a let-bindings type may contain raw tvars.
-- It may be necessary (eg. for codegen) to 're'generalise it once all free/escaped vars are resolved

-- Simplifications (Note. performed just before | during generalisation):
-- eg. foldr : (A → (C & B) → B) → C → μx.[Cons : {A , x} | Nil : {}] → (B & C)
-- =>  foldr : (A → B → B) → B → μx.[Cons : {A , x} | Nil : {}] → B
--  * remove polar variables `a&int → int => int→int` ; `int → a => int → bot`
--  * unify inseparable vars (polar co-occurence `a&b → a|b` and indistinguishables `a → b → a|b`)
--  * unify variables that have the same upper and lower bound (a<:t and t<:a) `a&int → a|int`
--  * tighten (roll) recursive types
--  * TODO: Type function subtyping: if A <: F A and F B <: B then A <: B

-- Generalisation is a 2 pass process
-- 1 Preparation & Analysis:
--   * read TVar bounds from Bisubs
--   * detect whether tvar cycles are guarded by TyCon (loops and recVars BitSets)
--   * save TVar co-occurences
--   * Co-occurence analysis: attempt to remove or unify tvars
-- 2. Finalise: Remove, unify or generalise (with possible mu binder) TVars depending on results of co-occurence analysis
generalise :: BitSet -> (Either IName Type) -> TCEnv s Type
generalise escapees rawType = let
  showTys t        = T.intercalate " , " (prettyTyRaw <$> t)
  traceCoocs nVars coocs = V.take nVars coocs `iforM` \i (p,m) -> traceM (show i <> ": + [" <> showTys p <> " ]; - [" <> showTys m <> "]")
  in do
  when global_debug (traceM $ "Gen: " <> show rawType)

  coocLen <- use bis <&> (900+) . MV.length -- + space for spawning let-bound instantiatables TODO
  (coOccurs .=) =<< MV.replicate coocLen ([],[])
  recVars .= 0
  -- merge with recTVar in case of direct recursion `r = { next = r } : µx.{next : x}`
  analysed   <- case rawType of
    Right ty -> substTypeMerge True emptyBitSet emptyBitSet ty
    Left recTVar -> mergeTypes True (TyVar recTVar) <$>
      substTypeVar True recTVar emptyBitSet emptyBitSet

  recursives <- use recVars
  occurs     <- V.unsafeFreeze =<< use coOccurs
  nVars      <- use blen
  leaks      <- use leakedVars
  let tvarSubs = judgeVars nVars escapees leaks recursives occurs
      -- If we subbed a recVar with a non-rec var, it lost the 'Recursive' tag
      -- (Obviously this patch is not ideal)
      fixedRecSubs = let
        updateV i val = V.modify (\mv -> MV.write mv i val)
        patchRec w v = case v V.! w of { SubVar x -> patchRec x v ; Generalise -> updateV w Recursive v ; _ -> v }
        go r v = case v V.! r of { SubVar w -> patchRec w v ; _ -> v }
        in foldr go tvarSubs (bitSet2IntList recursives)
      done = runST $ MV.replicate coocLen (complement 0) >>= \biEquis ->
        subGen fixedRecSubs{-tvarSubs-} leaks analysed `evalStateT` (GenEnvState [] emptyBitSet 0 0 biEquis)

  (done <$) $ when global_debug $ do
    traceCoocs nVars occurs
    traceM $ "analysed: " <> prettyTyRaw analysed
    traceM $ "escapees: " <> show (bitSet2IntList escapees)
    traceM $ "leaked:   " <> show (bitSet2IntList leaks)
    traceM $ "recVars:  " <> show (bitSet2IntList recursives)
    traceM   "tvarSubs: " *> V.imapM_ (\i f -> traceM $ show i <> " => " <> show f) tvarSubs
    traceM $ "done: "     <> (prettyTyRaw done)

-- co-occurence with v in TList1 TList2: find a tvar or a type that always cooccurs with v
-- hoping to unify v with its co-occurence (straight up remove it if unifies with a var)
-- opposite co-occurence: v + T always occur together at +v,-v => drop v (unify with T)
-- polar co-occurence:    v + w always occur together at +v,+w or at -v,-w => unify v with w
-- ? unifying recursive and non-recursive vars (does the non-rec var need to be covariant ?)
data VarSub = Remove | Escaped | Generalise | Recursive | SubVar Int | SubTy Type deriving Show
judgeVars :: Int -> BitSet -> BitSet -> BitSet -> V.Vector ([Type] , [Type]) -> V.Vector VarSub
judgeVars nVars escapees leaks recursives coocs = V.constructN nVars $ \prevSubs -> let
  collectCoocVs = \case { [] -> 0 ; x : xs -> foldr (.&.) x xs }
  v = V.length prevSubs -- next var to analyse
  vIsRec = recursives `testBit` v
  (pOccs , mOccs) = coocs V.! v
  prevTVs = setNBits v -- sub in solved vars rather than redoing cooccurence analysis on them
  subPrevVars :: Bool -> Type -> Type
  subPrevVars pos ty = let
    (tvars , rest) = partitionType ty
    subVar w = let self = TyVars (setBit 0 w) [] in if w >= v then self else case prevSubs V.! w of
      Remove     -> TyGround []
      Escaped    -> self
      Generalise -> self
      Recursive  -> self
      SubTy t    -> t
      SubVar x   -> subVar x
    in mergeTypeList pos $ [TyVars (complement prevTVs .&. tvars) [] , TyGround rest]
                    ++ (subVar <$> bitSet2IntList (prevTVs .&. tvars))
  ((pVars , pTs) , (mVars , mTs)) = ( unzip $ partitionType . subPrevVars True  <$> pOccs
                                    , unzip $ partitionType . subPrevVars False <$> mOccs)
  (coocPVs , coocMVs) = (collectCoocVs pVars , collectCoocVs mVars)

  in if -- Simplify: Try hard to justify Remove, failing that Sub, otherwise must Generalise
  | escapees `testBit` v -> Escaped -- belongs to a parent of this let-binding
  | not vIsRec && (null pOccs || null mOccs) -> Remove -- 'polar' var
  | otherwise -> let
    polarCooc :: Bool -> Int -> VarSub = \pos w -> let -- +: for ws in +v, look for coocs in +v,+w
      wCoocs = coocs V.! w ; wCooc = if pos then fst wCoocs else snd wCoocs
      cooc w (vs , vTs) (ws , wTs) = if (collectCoocVs (vs ++ ws) `clearBit` v) /= 0
        then SubVar w else Generalise
      in {-d_ (v , w , pos) $-}
      if null (fst wCoocs) || null (snd wCoocs)
      then Generalise -- don't merge with a polar (or recursive variable)
      else cooc w (if pos then (pVars , pTs) else (mVars , mTs))
        $ (unzip $ partitionType . subPrevVars pos <$> wCooc)
    polarCoocs pos vCoocs = let -- search ws found in v+ (or v-)
      -- ? should avoid unifying rec and non-rec vars ?
      -- recMask = if vIsRec then recursives else complement recursives
      -- Note. we already attempted to unify w<v with v, so only try w>v
      ws = ({- recMask .&. -} complement prevTVs .&. vCoocs) `clearBit` v
      in polarCooc pos <$> bitSet2IntList ws

    -- in v+v- if v coocs with w then it always does, so "unify v with w" means "remove v"
    -- but in v+w+ or v-w- no shortcuts: "unify v with w" means "replace occurs of v with w"
    vPvM = if collectCoocVs (pVars ++ mVars) `clearBit` v /= 0 then Remove else Generalise
    vPwP = polarCoocs True  coocPVs :: [VarSub]
    vMwM = polarCoocs False coocMVs :: [VarSub]
    -- look for some T present at all v+v- (since this is expensive and rarer try it last) `A & %i32 -> A & %i32`
    vTs = let allCoocs = concat (pTs ++ mTs) in maybe Generalise (\t -> SubTy (TyGround [t]))
      $ join $ head <$> head
      (filter ((== length pTs + length mTs) . length) (group {-$ sort-} allCoocs))
      -- need to sort since group only joins adjacent elements (but that requires Ord on Types)
      -- TODO tycon Intersects eg. { a : t , b : _ } and { a : T } have a co-occurence { a : T }
--  intersectCooc :: [TyHead] -> [TyHead] -> [TyHead] = \t intersects -> let -- valid cooc intersections
--    intersectTH th intersect

    -- use foldl' to stop once we've found a reason to either Remove or Sub the tvar
    bestSub ok next = case ok of { Remove->ok ; (SubTy t)->ok ; (SubVar v)->ok ; ko->next }
--  doRec s = if recursives `testBit` v && (null pTs || null mTs) then case s of { Generalise -> Recursive ; _ -> s} else s
    doRec s = if recursives `testBit` v then case s of { Generalise -> Recursive ; _ -> s} else s
    in doRec $ foldl' bestSub vPvM (vPwP ++ vMwM) `bestSub` vTs

-- Final step; use VarSubs to eliminate all TVars
-- Also attempt to roll µtypes
subGen :: V.Vector VarSub -> BitSet -> Type -> GenEnv s Type
subGen tvarSubs leakedVars raw = use biEqui >>= \biEqui' -> let
  generaliseRecVar v = MV.read biEqui' v >>= \perm -> if perm /= complement 0
    then perm <$ (hasRecs %= (`setBit` v)) else do -- xyz recursive vars fresh names
      m <- quantsRec <<%= (+1)
      when global_debug (traceM $ show v <> " =>µ " <> toS (number2xyz m))
      m <$ MV.write biEqui' v m
  generaliseVar v = MV.read biEqui' v >>= \perm -> if perm /= complement 0
    then pure perm else do -- A..Z generalised vars fresh names
      q <- quants <<%= (+1)
      when global_debug (traceM $ show v <> " =>∀ " <> toS (number2CapLetter q))
      q <$ MV.write biEqui' v q

  doVar pos v = case tvarSubs V.! v of
    Escaped  -> pure (TyVar v)
    Remove   | leakedVars `testBit` v -> pure (TyVar v)
    Remove   -> pure (TyGround [])
    Generalise | leakedVars `testBit` v -> generaliseVar v <&> \q -> mergeTVar v (TyGround [THBound q])
    Generalise -> generaliseVar v <&> \q -> TyGround [THBound q]
    Recursive  -> (hasRecs %= (`setBit` v)) *> generaliseRecVar v <&> \m -> TyGround [THMuBound m]
    SubVar i   -> doVar pos i
    SubTy t    -> goType pos t -- pure t

  -- attempt to roll outer layers of t into a µ type contained within
  rollMu t@(TyGround [THMu m t2]) = pure t -- $ case t2 of { TyGround [THMu n t3] | n == m -> t3 ; _ -> t }
--rollMu t = pure t -- disable rollMu
  rollMu t = use muWrap >>= \case
    [] -> pure t
    x@(recBranch , m , mt , invMuStart , invMu) : xs -> do
      when global_debug (traceM $ "roll µ? " <> prettyTyRaw t) -- <> "\n  invMu = " <> show invMu)
      when (global_debug && not (null xs)) (traceM $ ">1 MuInvs: " <> show (length (x : xs))) --show (x : xs))
      case (\inv -> testWrapper inv recBranch t) <$> invMu of
        [] -> t <$ (muWrap .= [])
        [x] -> case x of
          Left invMuNext -> t <$ (muWrap .= [(error "recBranch not set" , m , mt , invMuStart , [invMuNext])])
          Right False    -> t <$ (muWrap .= [])
          Right True     -> let rolled = case mt of { TyGround [THMu n t] | n == m -> mt ; _ -> TyGround [THMu m mt] } in do
            when global_debug (traceM $ "Rolled µ! " <> prettyTyRaw t
                                   <> "\n       => " <> prettyTyRaw rolled)
            rolled <$ (muWrap .= []) -- (muWrap .= Just (m , mt , invMuStart , invMuStart))
        xs -> t <$ (muWrap .= []) -- error $ show xs

  checkRec vs wrappedRecs t = let
    go t v = MV.read biEqui' v >>= \m -> let
      mT    = rmMuBound m t
      invMu = invertMu (startInvMu m) mT
      in TyGround [THMu m mT] <$ ((muWrap .= [(_ , m , mT , invMu , invMu)])) -- *> traceShowM invMu)
    in foldM go t (bitSet2IntList (vs .&. wrappedRecs))

  goType pos = \case
    TyVars vs g -> do
      -- ground types first for naming priority: `(A -> B) & B` rather than `(B -> A) & A`
      grounds <- finaliseTyHead pos `mapM` g
      recs <- use hasRecs
      vars <- doVar pos `mapM` bitSet2IntList vs
      if null grounds then pure (mergeTypeList pos vars)
        else checkRec vs recs (mergeTypeList pos (grounds ++ vars))
    TyVar v    -> doVar pos v -- >>= checkRec (0 `setBit` v)
    TyGround g -> mergeTypeList pos <$> finaliseTyHead pos `mapM` g

  -- Indicate which tycon branch a mu-type came from
  updateMu recBranch = \case { []->[] ; [(lastI,m,mT,invS,invC)] -> [(recBranch,m,mT,invS,invC)] }
  goGuarded pos branch t = do
    t   <- goType pos t
    mus <- muWrap <<.= []
    pure (tyLatticeEmpty pos t , updateMu branch mus)

  finaliseTyHead pos th = (\(x , m) -> (muWrap .= m) *> rollMu (TyGround [x])) =<< case th of
    THBi b ty -> (,[]) . THBi b <$> goType pos ty
--  THMu m (TyGround [mu@(THMu n t)]) | m == n -> pure (mu , [])
    -- for tycons, collect the branch ids so rollMu knows which recursive branch the mu came from
    THTyCon t   -> let addBranches = snd . BSM.mapAccum (\n val -> (n+1 , (n,val))) 0
      in (\(t,m) -> (THTyCon t , m)) <$> case t of
      THArrow ars r -> do
        branches <- traverse (uncurry (goGuarded (not pos))) (zip [1..] ars)
        ret      <- goGuarded pos 0 r
        pure (THArrow (fst <$> branches) (fst ret) , concat (snd ret : (snd <$> branches)))
      THTuple     r -> do
        branches <- V.imapM (goGuarded pos) r
        pure (THTuple (fst <$> branches) , concat (V.toList (snd <$> branches)))
      THProduct   r -> do
        branches <- traverse (\(i,t) -> goGuarded pos i t) (addBranches r)
        pure (THProduct (fst <$> branches) , concat (snd <$> BSM.elems branches))
      THSumTy     r -> do
        branches <- traverse (\(i,t) -> goGuarded pos i t) (addBranches r)
        pure (THSumTy (fst <$> branches) , concat (snd <$> BSM.elems branches))
    x -> pure (x , [])
  in (fst <$> goGuarded True 0 raw) >>= \done -> use quants <&> \q ->
    if q > 0 then TyGround [THBi q done] else done

--------------------
-- Analysis Phase --
--------------------
-- Read typevars from Bisubs, collect co-occurences and identify recursive types
-- non-escaped typevars are possibly safe to cache their substitution to
registerOccurs :: Bool -> Type -> TCEnv s Type
registerOccurs pos ty = use coOccurs >>= \cooc -> let
  (vset , other)    = partitionType ty
  in ty <$ bitSet2IntList vset `forM` \i ->
    MV.modify cooc (over (if pos then _1 else _2) (TyVars vset other :)) i

substTypeVar :: Bool -> Int -> BitSet -> BitSet -> TCEnv s Type
substTypeVar pos v loops guarded = if
  | testBit loops v   -> pure (TyVars loops []) -- unguarded var loop
  | testBit guarded v -> TyVars (0 `setBit` v) [] <$ (recVars %= (`setBit` v))
  | otherwise -> use bis >>= \b -> MV.read b v >>= \(BiSub pty mty) -> let -- not atm a TVar cycle
    loops'    = setBit loops v
    ty = if pos then pty else mty
    in if nullType ty
       then pure $ TyVars loops' []
       else substTypeMerge pos loops' guarded ty

substTypeMerge :: Bool -> Integer -> Integer -> Type -> TCEnv s Type
substTypeMerge pos loops guarded ty =  let
  (tvars , others) = partitionType ty
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
    t@THExt{}  -> pure $ TyGround [t]
    t@THTop{}  -> pure $ TyGround [t]
    t@THBot{}  -> pure $ TyGround [t]
    THBi n t -> instantiate n t >>= substGuarded pos  -- a generalised let-bound function
    THMu m t -> instantiate 0 (TyGround [THMu m t]) >>= substGuarded pos
--  ^ Maybe can avoid insantiating here
{-  THBi n t -> use quants >>= \q-> if q /= 0 then _ else (quants .= n) *> substGuarded pos t
--  THBound t -> THBound t
    THMu m t -> (recQuants %= (\m -> if m /= 0 then _ else m+1)) *> substGuarded pos t
    THMuBound m -> THMuBound m
      --substGuarded pos (mergeTypes (TyGround [THMuBound m]) t)
-}
--  THMu m t -> substGuarded pos t
    x -> error $ show x --pure [x]
  in do
    vs <- bitSet2IntList tvars `forM` \x -> mergeTVar x <$> substTypeVar pos x loops guarded
    ts <- substTyHead `mapM` others
    pure (mergeTypeList pos (vs ++ ts))
