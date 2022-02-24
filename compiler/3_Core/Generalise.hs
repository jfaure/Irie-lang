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
import qualified Data.IntMap as IM (mapAccum)

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
--  * ? A → A & Int =? Int → Int
--  * remove polar variables `a&int → int => int→int` ; `int → a => int → bot`
--  * unify inseparable vars (polar co-occurence `a&b → a|b` and indistinguishables `a→b→a|b`)
--  * unify variables that have the same upper and lower bound (a<:t and t<:a) `a&int→a|int`
--  * tighten (roll) recursive types
--  * TODO: Type function subtyping: if A <: F A and F B <: B then A <: B

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
  (quants .= 0) *> (quantsRec .= 0) *> (muWrap .= Nothing) *> (hasRecs .= 0)

  bs <- use bis
  let coocLen = MV.length bs + 100 -- + let-bound instantiatables TODO (perhaps ignore | Generalise any tvars > coocLen?)
  (biEqui .=)   =<< MV.replicate coocLen (complement 0)
  (coOccurs .=) =<< MV.replicate coocLen ([],[])
  recVars .= 0

  analysed   <- substTypeVar True recTVar emptyBitSet emptyBitSet
  recursives <- use recVars
  occurs     <- use coOccurs
  occLen     <- use blen
  when global_debug (traceCoocs occLen occurs)
  leaks    <- use leakedVars 
  tvarSubs <- coocVars occLen escapees leaks recursives <$> V.unsafeFreeze occurs

  when global_debug $ do
    traceM $ "analysed: " <> prettyTyRaw analysed
    traceM $ "escapees: " <> show (bitSet2IntList escapees)
    traceM $ "leaked:   " <> show (bitSet2IntList leaks)
    traceM $ "recVars:  " <> show (bitSet2IntList recursives)
    traceM   "tvarSubs: " *> V.imapM_ (\i f -> traceM $ show i <> " => " <> show f) tvarSubs

  -- merge with recTVar in case of direct recursion `r = { next = r } : µx.{next : x}`
  done <- subGen tvarSubs (mergeTypes True (TyVar recTVar) analysed)
  when global_debug $ traceM $ "done: " <> (prettyTyRaw done)
  pure done

-- co-occurence with v in TList1 TList2: find a tvar or a type that always cooccurs with v
-- hoping to unify v with its co-occurence (straight up remove it if unifies with a var)
-- * unifying recursive and non-recursive vars is only admissible if the non-rec var is covariant
-- opposite co-occurence: v + T always occur together at +v,-v => drop v (unify with T)
-- polar co-occurence:    v + w always occur together at +v,+w or at -v,-w => drop v (unify with w)
data VarSub = Remove | Escaped | Generalise | Recursive | SubVar Int | SubTy Type deriving Show
--coocVars occLen escapees recursives coocs = V.constructN occLen $ \prevSubs -> let
coocVars :: Int -> BitSet -> BitSet -> BitSet -> V.Vector ([Type] , [Type]) -> V.Vector VarSub
coocVars occLen escapees leaks recursives coocs = V.constructN occLen $ \prevSubs -> let
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

  -- look if v always (v+v-) coocs with some T, in which case we can remove v
  coocType pTs mTs = case Nothing of
    Just t  -> SubTy t
    Nothing -> Generalise

  in if -- Simplify: Try hard to justify Remove, failing that Sub, otherwise must Generalise
  | escapees `testBit` v -> Escaped -- belongs to a parent of this let-binding
  | not vIsRec && (null pOccs || null mOccs) -> Remove -- 'polar' var
  | otherwise -> let
    polarCooc :: Bool -> Int -> VarSub -- eg. + case: for all w in +v, look for coocs in +v,+w
    polarCooc pos w = let -- check in v+w+ and v-w- if w polar co occurs with v
      wCoocs = coocs V.! w ; wCooc = if pos then fst wCoocs else snd wCoocs
      cooc w (vs , vTs) (ws , wTs) = if (collectCoocVs (vs ++ ws) `clearBit` v) /= 0
        then SubVar w else coocType vTs wTs
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
    vPvM = if collectCoocVs (pVars ++ mVars) `clearBit` v /= 0 then Remove else coocType pTs mTs
    vPwP = polarCoocs True  coocPVs :: [VarSub]
    vMwM = polarCoocs False coocMVs :: [VarSub]
    -- use foldl' to stop once we've found a reason to either Remove or Sub the tvar
    bestSub ok next = case ok of { Remove -> ok ; (SubTy t) -> ok ; (SubVar v) -> ok ; ko -> next }
--  doRec s = if recursives `testBit` v && (null pTs || null mTs) then case s of { Generalise -> Recursive ; _ -> s} else s
    doRec s = if recursives `testBit` v then case s of { Generalise -> Recursive ; _ -> s} else s
    in doRec $ foldl' bestSub vPvM (vPwP ++ vMwM)

-- Final step; use VarSubs to eliminate all TVars (sub with THBound|THMuBound or remove)
subGen :: V.Vector VarSub -> Type -> TCEnv s Type
subGen tvarSubs raw = use bis >>= \b -> use biEqui >>= \biEqui' -> use coOccurs >>= \coocs -> let
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

  doVar pos v = use leakedVars >>= \leaks -> case tvarSubs V.! v of
    Escaped  -> pure (TyVar v)
    Remove   | leaks `testBit` v -> pure (TyVar v)
    Remove   -> pure (TyGround [])
    Generalise | leaks `testBit` v -> generaliseVar v <&> \q -> mergeTVar v (TyGround [THBound q])
    Generalise -> generaliseVar v <&> \q -> TyGround [THBound q]
    Recursive  -> (hasRecs %= (`setBit` v)) *> generaliseRecVar v <&> \m -> TyGround [THMuBound m]
    SubVar i   -> doVar pos i
    SubTy t    -> goType pos t -- pure t

  -- attempt to roll outer layers of t into a µ type contained within
  rollMu recBranch t@(TyGround [THMu{}]) = pure t
  rollMu recBranch t = use muWrap >>= \case
    Nothing -> pure t
    Just (m , mt , invMuStart , invMu) ->
      when global_debug (traceM $ "roll µ? " <> prettyTyRaw t {-<> " ; " <> show invMu-})
      *> case (\inv -> testWrapper inv recBranch t) <$> invMu of
        [] -> t <$ (muWrap .= Nothing)
        [x] -> case x of
          Left invMuNext -> t <$ (muWrap .= Just (m , mt , invMuStart , [invMuNext]))
          Right False    -> t <$ (muWrap .= Nothing)
          Right True     -> let rolled = TyGround [THMu m mt] in do
            when global_debug (traceM $ "Rolled µ! " <> prettyTyRaw t
                                   <> "\n       => " <> prettyTyRaw rolled)
            rolled <$ (muWrap .= Just (m , mt , invMuStart , invMuStart))
        xs -> t <$ (muWrap .= Nothing) -- error $ show xs

  checkRec vs wrappedRecs t = let
    go t v = MV.read biEqui' v >>= \m -> let
      mT    = rmMuBound m t
      invMu = invertMu Nothing mT
      in TyGround [THMu m mT] <$ (muWrap .= Just (m , mT , invMu , invMu))
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
  goGuarded pos branch t = tyLatticeEmpty pos <$> (goType pos t >>= rollMu branch) -- TODO is this right branch/type pair?
  finaliseTyHead pos th = (\x -> TyGround [x]) <$> case th of
    THBi b ty -> THBi b <$> goType pos ty
    -- for tycons, collect the branch ids so rollMu knows which recursive branch came from
    THTyCon t   -> let addBranches = snd . IM.mapAccum (\n val -> (n+1 , (n,val))) 0
      in THTyCon  <$> case t of
      THArrow ars r -> THArrow   <$> traverse (uncurry (goGuarded (not pos))) (zip [1..] ars)
                                 <*> (goGuarded pos 0 r)
      THTuple     r -> THTuple   <$> V.imapM  (goGuarded pos) r
      THProduct   r -> THProduct <$> traverse (\(i,t) -> goGuarded pos i t) (addBranches r)
      THSumTy     r -> THSumTy   <$> traverse (\(i,t) -> goGuarded pos i t) (addBranches r)
    x -> pure x
  in goGuarded True 0 raw >>= \done -> use quants <&> \q ->
    if q > 0 then TyGround [THBi q done] else done

--------------------
-- Analysis Phase --
--------------------
-- Read typevars from Bisubs, collect co-occurences and identify recursive types
-- non-escaped typevars are possibly safe to cache their substitution to (=<< updateVar)

-- tvars need to know what they co-occur with, for simplification purposes
registerOccurs :: Bool -> Type -> TCEnv s Type
registerOccurs pos ty = use coOccurs >>= \cooc -> let
  (vset , other)    = partitionType ty
  in ty <$ bitSet2IntList vset `forM` \i ->
    MV.modify cooc (over (if pos then _1 else _2) (TyVars vset other :)) i

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
    t@THExt{}  ->  pure $ TyGround [t]
    t@THTop{}  ->  pure $ TyGround [t]
    t@THBot{}  ->  pure $ TyGround [t]
    THBi n t -> instantiate n t >>= substGuarded pos  -- a generalised let-bound function
    THMu m t -> instantiate 0 (TyGround [THMu m t]) >>= substGuarded pos
--  Maybe can avoid insantiating here
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
