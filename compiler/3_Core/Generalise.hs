-- Biunfication records constraints , generalisation makes sense of them
module Generalise (generalise,) where
import BiUnify ( instantiate )
import Control.Lens -- ( iforM_, use, (<<%=), (<<.=), (%=), (.=), over, Field1(_1), Field2(_2) )
import CoreSyn ( global_debug, BiSub(BiSub), TyCon(THTuple, THArrow, THProduct, THSumTy , THSumOpen), TyHead(THMu, THBound, THMuBound, THTyCon, THPrim, THExt, THTop, THBot, THBi),
      Type(TyGround, TyVar, TyVars) )
import CoreUtils --( mergeTVars, mapType, invertMu, mergeTVar, mergeTypeList, mergeTypes, nullType, partitionType, startInvMu, testWrapper, tyLatticeEmpty )
import PrettyCore ( number2CapLetter, prettyTyRaw )
import TCState
import qualified BitSetMap as BSM ( elems, traverseWithKey )
import qualified Data.Vector.Mutable as MV ( length, modify, read, replicate, write )
import qualified Data.Text as T -- ( intercalate )
import qualified Data.Vector as V ( Vector, (!), cons, constructN, imapM, imapM_, length, take, toList, unsafeFreeze )

-- Simplification removes (or unifies with another type) as many tvars as possible
-- Generalisation allows polymorphic types to be instantiated with fresh tvars on each use.
-- This means some tvars are to be promoted to polymorphic vars
-- TVars and let-bindings:
-- 1. Escaped : tvars belong to outer let-nests, don't generalise (leave the raw tvar)
-- 2. Leaked  : local vars biunified with escaped vars (generalise and merge with raw tvar)
--   * necessary within let-binds to constrain free variables. considered dead outside the let-bind
-- 3. Dead    : formerly leaked vars once their scope expires. They are now overconstrained since were biunified with instantiations of their let-binding (they're present outside of their let binding due to at one point leaking through a constraint)
--
-- Setup:
--   let a ; b in g: mark freevars of a and b as escaped during (only during! g)
--   restore freeVars once g is generalised
--
-- Escaped vars examples:
-- * f1 x = let y z = z in y   -- nothing can go wrong
-- * f2 x = let y   = x in y   -- if x generalised at y ⇒ f2 : a → b
-- * f3 x = let y y = x y in y -- similar
-- Note. because of escaped vars, a let-bindings type may contain raw tvars.
-- It may be necessary (eg. for codegen) to 're'generalise it once all free/escaped vars are resolved

-- Simplifications (Note. performed just before | during generalisation):
-- eg. foldr : (A → (C & B) → B) → C → μx.[Cons : {A , x} | Nil : {}] → (B & C)
-- ⇒  foldr : (A → B → B) → B → μx.[Cons : {A , x} | Nil : {}] → B
--  * remove polar variables `a&int → int ⇒ int→int` ; `int → a ⇒ int → bot`
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
generalise ∷ BitSet → (Either IName Type) → TCEnv s Type
generalise escapees rawType = let
  showTys t        = T.intercalate " ; " (prettyTyRaw <$> t)
  traceCoocs nVars coocs = V.take nVars coocs `iforM_` \i (p,m) → traceM (show i <> ": +[" <> showTys p <> " ]; -[" <> showTys m <> "]")
  in do
  when global_debug (traceM $ "Gen: " <> show rawType)

  coocLen ← use bis <&> (900+) . MV.length -- + space for spawning let-bound instantiatables TODO
  (coOccurs .=) =≪ MV.replicate coocLen ([],[])
  recVars .= 0
  -- merge with recTVar in case of direct recursion `r = { next = r } : µx.{next : x}`
  analysed   ← case rawType of
    Right ty     → substTypeMerge True emptyBitSet emptyBitSet ty
    Left recTVar → mergeTypes True (TyVar recTVar) <$>
      substTypeVar True recTVar emptyBitSet emptyBitSet

  recursives ← use recVars
  occurs     ← V.unsafeFreeze =≪ use coOccurs
  nVars      ← use blen
  leaks      ← use leakedVars
  exts       ← use externs
  let tvarSubs = judgeVars nVars escapees leaks recursives occurs
      done = runST $ do
        biEquis   ← MV.replicate coocLen (complement 0)
        muBounds' ← MV.replicate coocLen (TyGround [])
        subGen tvarSubs leaks analysed `evalStateT` (GenEnvState [] exts emptyBitSet emptyBitSet 0 0 biEquis muBounds')

  (done <$) $ when global_debug $ do
    traceCoocs nVars occurs
    traceM $ "analysed: " <> prettyTyRaw analysed
    traceM $ "escapees: " <> show (bitSet2IntList escapees)
    traceM $ "leaked:   " <> show (bitSet2IntList leaks)
    traceM $ "recVars:  " <> show (bitSet2IntList recursives)
    traceM   "tvarSubs: " *> V.imapM_ (\i f → traceM $ show i <> " ⇒ " <> show f) tvarSubs
    traceM $ "done: "     <> prettyTyRaw done

-- co-occurence with v in TList1 TList2: find a tvar or a type that always cooccurs with v
-- hoping to unify v with its co-occurence (straight up remove it if unifies with a var)
-- opposite co-occurence: v + T always occur together at +v,-v ⇒ drop v (unify with T)
-- polar co-occurence:    v + w always occur together at +v,+w or at -v,-w ⇒ unify v with w
-- ? unifying recursive and non-recursive vars (does the non-rec var need to be covariant ?)
data VarSub = Remove | Escaped | Generalise | SubVar Int | SubTy Type deriving Show
judgeVars ∷ Int → BitSet → BitSet → BitSet → V.Vector ([Type] , [Type]) → V.Vector VarSub
judgeVars nVars escapees _leaks recursives coocs = V.constructN nVars $ \prevSubs → let
  collectCoocVs = \case { [] → 0 ; x : xs → foldr (.&.) x xs }
  v = V.length prevSubs -- next var to analyse
  vIsRec = recursives `testBit` v
  (pOccs , mOccs) = coocs V.! v
  prevTVs = setNBits v -- sub in solved vars rather than redoing cooccurence analysis on them
  subPrevVars ∷ Bool → Type → Type
  subPrevVars pos ty = let
    (tvars , rest) = partitionType ty
    subVar w = let self = TyVars (setBit 0 w) [] in if w >= v then self else case prevSubs V.! w of
      Remove     → TyGround []
      Escaped    → self
      Generalise → self
      SubTy t    → t
      SubVar x   → subVar x
    in mergeTypeList pos $ [TyVars (complement prevTVs .&. tvars) [] , TyGround rest]
                    ++ (subVar <$> bitSet2IntList (prevTVs .&. tvars))
  ((pVars , pTs) , (mVars , mTs)) = ( unzip $ partitionType . subPrevVars True  <$> pOccs
                                    , unzip $ partitionType . subPrevVars False <$> mOccs)
  (coocPVs , coocMVs) = (collectCoocVs pVars , collectCoocVs mVars)

  in if -- Simplify: Try to justify Remove next Sub else fallback to Generalise
  | escapees `testBit` v → Escaped -- belongs to a parent of this let-binding
  | not vIsRec && (null pOccs || null mOccs) → Remove -- 'polar' var
  | otherwise → let
    recMask = if vIsRec then recursives else complement recursives
    polarCooc ∷ Bool → Int → VarSub = \pos w → let -- +: for ws in +v, look for coocs in +v,+w
      wCoocs = coocs V.! w
      wTypes = unzip $ partitionType . subPrevVars pos <$> (if pos then fst wCoocs else snd wCoocs)
      cooc w (vs , _vTs) (ws , _wTs) = if (collectCoocVs (vs ++ ws) `clearBit` v) /= 0 then SubVar w else Generalise
      in {-d_ (v , w , pos) $-} if (null (fst wCoocs) || null (snd wCoocs))
      then Generalise -- don't merge with a polar (or recursive variable)
      else cooc w (if pos then (pVars , pTs) else (mVars , mTs)) wTypes

    -- search ws found in v+ (or v-) note. we already attempted all w < v , but there may still be matches in the other var
    polarCoocs pos vCoocs = polarCooc pos <$> bitSet2IntList (vCoocs `clearBit` v)

    -- in v+v- if non-recursive v coocs with w then it always does, so "unify v with w" means "remove v"
    -- but in v+w+ or v-w- no shortcuts: "unify v with w" means "replace occurs of v with w"
    -- avoid unifying rec and non-rec vars (recMask .&.)
    vPvM = case bitSet2IntList $ (recMask .&. collectCoocVs (pVars ++ mVars)) `clearBit` v of
      w : _ → if vIsRec then SubVar w else Remove
      _     → Generalise
    -- Aggressively merge recursive vars even if only partial co-occurence
    vPvMRec = let partialRecCoocs = complement prevTVs .&. recMask .&. foldr (.|.) 0 (pVars ++ mVars) `clearBit` v
      in if vIsRec then maybe Generalise SubVar (head (bitSet2IntList partialRecCoocs)) else Generalise

    -- recmask to disallow merge x & A in (x & A) → (µx.[Cons {%i32 , x}] & A)
    vPwP = polarCoocs True  ({-recMask .&.-} coocPVs) ∷ [VarSub]
    vMwM = polarCoocs False ({-recMask .&.-} coocMVs) ∷ [VarSub]
    -- look for some T present at all v+v- (since this is expensive and rarer try it last) `A & %i32 → A & %i32`
    vTs = let allCoocs = concat (pTs ++ mTs) in maybe Generalise (\t → SubTy (TyGround [t]))
      $ head =≪ head (filter ((== length pTs + length mTs) . length) (group {-$ sort-} allCoocs))
      -- need to sort since group only joins adjacent elements (but that requires Ord on Types)
      -- TODO tycon Intersects eg. { a : t , b : _ } and { a : T } have a co-occurence { a : T }
--  intersectCooc ∷ [TyHead] → [TyHead] → [TyHead] = \t intersects → let -- valid cooc intersections
--    intersectTH th intersect

    -- use foldl' to stop once we've found a reason to either Remove or Sub the tvar
    bestSub ok next = case ok of { Remove → ok ;  SubTy _ → ok ; SubVar _ → ok ; _ko → next }
    in foldl' bestSub (vPvM `bestSub` vPvMRec) (vPwP ++ vMwM) `bestSub` vTs

-- Final step; use VarSubs to eliminate all (unleaked & unescaped) TVars
-- Also attempt to roll µtypes
subGen ∷ V.Vector VarSub → BitSet → Type → GenEnv s Type
subGen tvarSubs leakedVars raw = use biEqui ≫= \biEqui' → let
  generaliseRecVar = generaliseVar
  generaliseVar v = MV.read biEqui' v ≫= \perm → if perm /= complement 0
    then pure perm else do -- A..Z generalised vars fresh names
      q ← quants <<%= (+1)
      when global_debug (traceM $ show v <> " ⇒ ∀" <> toS (number2CapLetter q))
      q <$ MV.write biEqui' v q

  doVar pos v = use seenVars ≫= \seen → case tvarSubs V.! v of
    Escaped    → pure (TyVar v)
    Remove     | leakedVars `testBit` v → pure (TyVar v)
    Remove     → pure (TyGround [])
    Generalise | leakedVars `testBit` v → generaliseVar v <&> \q → mergeTVar v (TyGround [THBound q])
    Generalise | seen `testBit` v → (hasRecs %= (`setBit` v)) *> generaliseRecVar v <&> \q → TyGround [THMuBound q]
    Generalise → generaliseVar v <&> \q → TyGround [THBound q]
    SubVar i   → doVar pos i
    SubTy t    → goType pos t -- pure t

  -- attempt to roll outer layers of t into a µ type contained within
--rollMu t mwrap = pure t -- disable rollMu
  rollMu t mwrap = let
    tryInv (recBranch , m , mt , invMu) = when global_debug (traceM $ "roll µ? " <> prettyTyRaw t) *>
      case (\inv → testWrapper mt inv recBranch t) <$> invMu of
        [] → pure Nothing
        (x:xss) → let
          doWrap x = case x of -- Left = need to test more wraps ; Right Bool = unrolling OK | KO
            Left invMuNext → Nothing <$ (muWrap .= [(error "recBranch not set" , m , mt , [invMuNext])])
            Right Nothing  → pure Nothing
            Right (Just x) → let rolled = TyGround [THMu m x] in Just rolled <$
              when global_debug (traceM $ "Rolled µ! " <> prettyTyRaw t
                                     <> "\n     ⇒ " <> prettyTyRaw rolled)
              <* when (global_debug && not (null xss)) (traceM $ show xss) -- rec1
          in doWrap x -- ? xss
    in do
      when (global_debug && not (null (drop 1 mwrap))) (traceM $ ">1 MuInvs: " <> show (length mwrap)) --show (x : xs))
      fromMaybe t <$> foldM (\x next → case x of { Nothing → tryInv next ; r → pure r }) Nothing mwrap

  -- Wrap a type in μ-binder of it's recursive typevars
  checkRec vs wrappedRecs t = let -- ! Hack; need to use SubVar to ensure the mus are merged out of scope
--  addMus ∷ [Int] → Type → GenEnv s Type
    addMus rawTVs t = (MV.read biEqui' `mapM` rawTVs) ≫= \vs → let
      rmVars m = let goGround = filter (\case { THBound x → not (m `testBit` x) ; THMuBound x → not (m `testBit` x) ; _ → True })
        in \case
        TyGround g  → TyGround  (goGround g)
        TyVars vs g → TyVars vs (goGround g)
        t → t
      mT = rmVars (intList2BitSet vs) t
      wraps = vs <&> \m → (_ , m , mT , invertMu m (startInvMu m) mT)
      retTy = foldl (\ty m → TyGround [THMu m ty]) mT vs
      in retTy <$ (muWrap %= (wraps ++ ))
    realRecList = bitSet2IntList (vs .&. wrappedRecs)
    addMuBounds t = (use muBounds ≫= \mb → [] {-realRecList-} `forM` \r → MV.read mb r)
      <&> \bounds → mergeTypeList True (t : bounds) -- TODO pos
    in addMuBounds t ≫= addMus realRecList ≫= mergeMus

  -- weird patch logic to eliminate eq mubounds: μa.μb.{ x : a , y : b } ⇒ μa.{x : a , y : b}
  mergeMus = let
    doMerge m n t = let
      newM = min m n
      oldM = max m n
      go = \case
        THMuBound x | x == oldM → THMuBound newM
        THMu x t    | x == oldM → THMu newM t
        x → x
      newT = if m == n then t else mapType go t
      in when (oldM /= newM) (traceM ("mergemu: " <> show oldM <> " ⇒ " <> show newM ∷ Text))
        *> (muWrap .= [(_ , newM , newT , invertMu newM (startInvMu newM) newT)])
        $> TyGround [THMu newM newT]
    in \case
      TyGround [THMu m (TyGround [THMu n t])]        → doMerge m n t
      TyGround [THMu m (TyGround ty) , THMuBound n]  → doMerge m n (TyGround ty)
      TyGround [THMuBound n , THMu m (TyGround ty)]  → doMerge m n (TyGround ty)
      t → pure t

  goType pos t = let
    finaliseTyHead pos th = subBranches pos th ≫= \(x , m) → rollMu (TyGround [x]) m
    -- since recursive tvars may be subbed , we need to get to the bottom of var subs immediately (for checkRec)
    subvar v = case tvarSubs V.! v of
      SubVar w → subvar w
      _        → v
    subvars vs = intList2BitSet (subvar <$> bitSet2IntList vs)
    in case t of
    TyVars vs' g → let vs = subvars vs' in do
      svSeenVars ← seenVars <<%= (.|. vs)
      -- ground types first for naming priority: `(A → B) & B` rather than `(B → A) & A`
      svRecs  ← hasRecs <<.= 0
      grounds ← finaliseTyHead pos `mapM` g
      seenVars .= svSeenVars
      recs ← hasRecs <<%= (.|. svRecs)
      vars ← mergeTypeList pos <$> (doVar pos `mapM` bitSet2IntList vs)

      newRecs ← (.&. complement recs) <$> use hasRecs
      use muBounds ≫= \mb → bitSet2IntList newRecs `forM_` \r → MV.modify mb (\t → (mergeTypeList pos (t : grounds))) r
      let hasMu (TyGround t) = any (\case { THMuBound{} → True ; _ → False }) t
          hasMu _ = False

      if null grounds || hasMu vars -- TODO maybe not good enough since vars can contain groundtypes
        then pure vars
        else checkRec vs recs $ case vars of
          -- TODO if typemerge mu bound m & t , bubble t upwards to outer occurences of m
--        TyGround [THMuBound m] → trace ("!drop μ-merge " <> show m <> ": " <> prettyTyRaw (mergeTypeList pos grounds)) vars
          vars → (mergeTypeList pos (vars : grounds))
--  TyVar v    → (seenVars %= (`setBit` v)) *> doVar pos v -- ≫= checkRec (0 `setBit` v)
    TyVar v    → goType pos (TyVars (0 `setBit` v) [])
    TyGround g → goType pos (TyVars 0 g) -- mergeTypeList pos <$> finaliseTyHead pos `mapM` g
    x → error (show x) -- TyPi TySi TyAlias TyTerm

  -- Indicate which tycon branch a mu-type came from
  goGuarded _oldRecs pos branch guardedT = let
    updateMu recBranch = map (\(_lastI,m,mT,invC) → (recBranch,m,mT,invC))
    in do
    t   ← goType pos guardedT
    mus ← muWrap <<.= []
    pure (tyLatticeEmpty pos t , updateMu branch mus)

  subBranches pos th = use hasRecs ≫= \recVars → case th of
    THBi b ty → (,[]) . THBi b <$> goType pos ty
    -- for tycons, collect the branch ids so rollMu knows which recursive branch the mu came from
    THTyCon t   → (\(t,m) → (THTyCon t , m)) <$> case t of
      THArrow ars r → do
        -- prevent contravariant recursive types
        sv ← seenVars <<.= 0
        branches ← zipWithM (goGuarded recVars (not pos)) [1..] ars
        seenVars .= sv
        ret      ← goGuarded recVars pos 0 r
        pure (THArrow (fst <$> branches) (fst ret) , concatMap snd (ret : branches))
      THTuple     r → do
        branches ← V.imapM (goGuarded recVars pos) r
        pure (THTuple (fst <$> branches) , concatMap snd (V.toList branches))
      THProduct   r → do
        branches ← BSM.traverseWithKey (goGuarded recVars pos) r
        pure (THProduct (fst <$> branches) , concatMap snd (BSM.elems branches))
      THSumTy     r → do
        branches ← BSM.traverseWithKey (goGuarded recVars pos) r
        let sumT = THSumTy (fst <$> branches) 
            mT = TyGround [THTyCon sumT]
        -- | ! HACK for prependToAll
--      mwrap ← use hasRecs <&> \r → bitSet2IntList ((0 `setBit` 3)) <&> \m → (0 , m , mT , invertMu m (startInvMu m) mT)
        pure (sumT , {-mwrap ++-} concatMap snd (BSM.elems branches))
      THSumOpen r d → do
        branches ← BSM.traverseWithKey (goGuarded recVars pos) r
        open     ← goGuarded recVars pos (-1) d -- ! branch keys should never be negative TODO use prelude module
        pure (THSumOpen (fst <$> branches) (fst open) , concatMap snd (open `V.cons` BSM.elems branches))
    x → pure (x , [])

  in use seenVars ≫= \s → (fst <$> goGuarded s True 0 raw) ≫= \done → use quants <&> \q →
    if q > 0 then TyGround [THBi q done] else done

--------------------
-- Analysis Phase --
--------------------
-- Read typevars from Bisubs, collect co-occurences and identify recursive types
-- non-escaped typevars are possibly safe to cache their substitution to
registerOccurs ∷ Bool → Type → TCEnv s Type
registerOccurs pos ty = use coOccurs ≫= \cooc → let
  (vset , other)    = partitionType ty
  in ty <$ bitSet2IntList vset `forM` \i →
    MV.modify cooc (over (if pos then _1 else _2) (TyVars vset other :)) i

substTypeVar ∷ Bool → Int → BitSet → BitSet → TCEnv s Type
substTypeVar pos v loops guarded = if
  | testBit loops v   → pure (TyVars loops []) -- unguarded var loop
  | testBit guarded v → TyVars (0 `setBit` v) [] <$ (recVars %= (`setBit` v))
  | otherwise → use bis ≫= \b → MV.read b v ≫= \(BiSub pty mty) → let -- not atm a TVar cycle
    loops'    = setBit loops v
    ty = if pos then pty else mty
    in if nullType ty
       then pure (TyVars loops' [])
       else substTypeMerge pos loops' guarded ty

substTypeMerge ∷ Bool → Integer → Integer → Type → TCEnv s Type
substTypeMerge pos loops guarded ty =  let
  (tvars , others) = partitionType ty
  guarded' = guarded .|. loops .|. tvars
  substTyHead = let
    substGuarded p t = substTypeMerge p 0 guarded' t ≫= registerOccurs p
    in \case
    THTyCon t → (\x → TyGround [THTyCon x]) <$> case t of
      THArrow ars r → THArrow   <$> traverse (substGuarded (not pos)) ars
                                 <*> substGuarded pos r
      THProduct   r → THProduct <$> traverse (substGuarded pos) r
      THSumTy     r → THSumTy   <$> traverse (substGuarded pos) r
      THSumOpen r d → THSumOpen <$> traverse (substGuarded pos) r <*> substGuarded pos d
      THTuple     r → THTuple   <$> traverse (substGuarded pos) r
    t@THPrim{} → pure $ TyGround [t]
    t@THExt{}  → pure $ TyGround [t]
    t@THTop{}  → pure $ TyGround [t]
    t@THBot{}  → pure $ TyGround [t]
    THBi n t → instantiate pos n t ≫= substGuarded pos  -- a generalised let-bound function
--  THMu m t → instantiate 0 (TyGround [THMu m t]) ≫= substGuarded pos
    THMu m t → substGuarded pos (TyGround [THMu m t])
    x → error $ show x --pure [x]
  in do
  vs ← bitSet2IntList tvars `forM` \x → mergeTVar x <$> substTypeVar pos x loops guarded
  ts ← substTyHead `mapM` others
  pure (mergeTypeList pos (vs ++ ts))
