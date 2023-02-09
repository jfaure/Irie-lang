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
import qualified Data.List.NonEmpty as NE
import Data.Functor.Foldable
debug_gen = False || global_debug
fst3 (a,_,_) = a

-- TODO audit whether the ad-hoc handling of THBI instantiations works:
-- * if type-merges of THBound involved
-- * higher rank polymorphism (stacked THBi)

indexed :: Traversable f => f a -> f (Int , a)
indexed f = traverse (\t -> get >>= \i -> modify (1+) $> (i , t)) f `evalState` 0

-- Simplification removes (or unifies with another type) as many tvars as possible
-- Generalisation allows polymorphic types to be instantiated with fresh tvars on each use: promote tvar to Π-bound
-- Levels: lvlN bitmask = not generalisable at each lvl
-- tvars must never refer to deeper let-nest tvars through their bounds
-- unify (v <=> a -> b) => export a and b to level of v
-- Escaped vars examples:
-- * f1 x = let y z = z in y   -- nothing can go wrong
-- * f2 x = let y   = x in y   -- if x generalised at y then f2 : a -> b (Wrong)
-- * f3 x = let y y = x y in y -- same problem
-- Note. because of escaped vars, let-bound types may contain raw tvars, so
-- later (eg. for codegen) need to 're'generalise to sub out free/escaped vars once they're resolved

-- Simplifications (performed just before commiting to generalising a tvar):
-- eg. foldr : (A -> (C & B) -> B) -> C -> μx.[Cons : {A , x} | Nil : {}] -> (B & C)
-- =>  foldr : (A -> B       -> B) -> B -> μx.[Cons : {A , x} | Nil : {}] -> B
--  * remove polar variables `a&int -> int => int->int` ; `int -> a => int -> bot`
--  * unify inseparable vars (polar co-occurence `a&b -> a|b` and indistinguishables `a -> b -> a|b`)
--  * unify variables that have the same upper and lower bound (a<:t and t<:a) `a&int -> a|int` => int -> int
--  * tighten (roll) recursive types
--  * TODO: Type function subtyping: if A <: F A and F B <: B then A <: B
--  * Interesting case: drop : ∏ A B → %i32 → (µa.[Cons {⊤ , a} | Nil] ⊓ B) → ([Nil] ⊔ B)
--    ie. B <= µa.[Cons {⊤ , a} | Nil] && B >= [Nil]
--    Annotations can restrict this to eg. B = [Nil] or B = µa.[Cons {Integer , a} | Nil]

-- Generalisation is a 2 pass process
-- 1 Preparation & Analysis:
--   * read TVar bounds from Bisubs
--   * detect whether tvar cycles are guarded by TyCon (loops and recVars BitSets)
--   * save TVar co-occurences
--   * Co-occurence analysis: attempt to remove or unify tvars
-- 2. Finalise: Remove, unify or generalise (with possible mu binder) TVars based on co-occurence analysis

type Cooc s = MV.MVector s ([Type] , [Type])
data AnalyseState s = AnalyseState { _anaBis :: MV.MVector s BiSub , _recs :: BitSet , _instVars :: Int , _coocs :: Cooc s }; makeLenses ''AnalyseState
type AnaEnv s = StateT (AnalyseState s) (ST s)

--data AState s = AState { _arecs :: BitSet , _acoocs :: Cooc s }; makeLenses ''AState
--type AEnv s = StateT (AState s) (ST s)
--type Seed = (Type , Bool , BitSet , BitSet , Int)

data GState s = GState { _quants :: Int , _genMap :: MV.MVector s Int }; makeLenses ''GState
type GEnv s = StateT (GState s) (ST s)

data VarSub = Remove | Escaped | Generalise | Recursive | SubVar Int | SubTy Type deriving Show

generalise :: BitSet -> Either IName Type -> TCEnv s Type
generalise lvl0 rawType = do
  when debug_gen (traceM $ "Gen: " <> show rawType)
  coocLen <- (+1000) <$> use blen -- space for instantiated tvars
  bis' <- use bis
  bl   <- use blen
  (analysedType , recursives , occurs) <- lift $ do -- re-use same ST state thread to avoid copying bisubs
    coocVStart <- MV.replicate coocLen ([],[])

--  (ty , (AState recs coocV))
--    <- runStateT (analyseT bis' (((\x -> TyVars (setBit 0 x)) ||| identity) rawType , True , 0 , 0 , 0)) (AState 0 coocVStart)
    (ty , (AnalyseState _bis recs _instVs coocV)) <-
      -- merge with recTVar in case of direct recursion `r = { next = r } : µx.{next : x}`
      runStateT (analyseType (((\x -> TyVars (setBit 0 x) []) ||| identity) rawType) True 0 0) (AnalyseState bis' 0 bl coocVStart)
    occurs <- V.unsafeFreeze coocV
    pure (ty , recs , occurs)
  nVars  <- use blen
  let tvarSubs = judgeVars nVars lvl0 recursives occurs
      done     = forgetRoll . cata rollType $ runST $ do
        genMap  <- MV.replicate 8000 (complement 0) -- TODO
        (t , s) <- runStateT (cata (doGen tvarSubs recursives) analysedType True) (GState 0 genMap)
        pure $ if s._quants == 0 then t else TyGround [THBi s._quants t]

  (done <$) $ when debug_gen $ do
    let showTys t        = T.intercalate " ; " (prettyTyRaw <$> t)
     in V.take nVars occurs `iforM_` \i (p,m) -> traceM (show i <> ": +[" <> showTys p <> "] -[" <> showTys m <> "]")
    traceM $ "analysed: " <> prettyTyRaw analysedType
    traceM $ "lvl0: "     <> show (bitSet2IntList lvl0)
    traceM $ "recVars:  " <> show (bitSet2IntList recursives)
    traceM   "tvarSubs: " *> V.imapM_ (\i f -> traceM $ show i <> " => " <> show f) tvarSubs
    traceM $ "done: "     <> prettyTyRaw done

-- co-occurence with v in TList1 TList2: find a tvar or a type that always cooccurs with v
-- hoping to unify v with its co-occurence (straight up remove it if unifies with a var)
-- opposite co-occurence: v + T always occur together at +v,-v ⇒ drop v (unify with T)
-- polar co-occurence:    v + w always occur together at +v,+w or at -v,-w ⇒ unify v with w
-- ? unifying recursive and non-recursive vars (does the non-rec var need to be covariant ?)
judgeVars :: Int -> BitSet -> BitSet -> V.Vector ([Type] , [Type]) -> V.Vector VarSub
judgeVars nVars lvl0 recursives coocs = V.constructN nVars $ \prevSubs -> let
  collectCoocVs = \case { [] -> 0 ; x : xs -> foldr (.&.) x xs }
  v = V.length prevSubs -- next var to analyse
  vIsRec = recursives `testBit` v
  (pOccs , mOccs) = coocs V.! v
  prevTVs = setNBits v -- sub in solved vars rather than redoing cooccurence analysis on them
  subPrevVars :: Bool -> Type -> Type
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
  generalise = {-if leaks `testBit` v then Leaked else-} if vIsRec then Recursive else Generalise

  in if -- Simplify: Try to justify Remove next Sub else fallback to Generalise
-- | v >= tVars -> did_ $ if recursives `testBit` v then Recursive else Generalise -- Instantiated vars
  | lvl0 `testBit` v -> Escaped -- belongs to a parent of this let-binding
  | not vIsRec && (null pOccs || null mOccs) -> {-if leaks `testBit` v then Escaped else-} Remove --'polar' var
  | otherwise -> let
    recMask = if vIsRec then recursives else complement recursives
    polarCooc :: Bool -> Int -> VarSub = \pos w -> let -- +: for ws in +v, look for coocs in +v,+w
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
      -- !Cannot always shortcut to Remove; eg: v subvar w then remove w because w cooc x; wrong if v doesn't cooc x
      w : _ -> if True || vIsRec then SubVar w else Remove
      _     -> generalise

    -- Aggressively merge recursive vars even if only partial co-occurence
    vPvMRec = let partialRecCoocs = complement prevTVs .&. recMask .&. foldr (.|.) 0 (pVars ++ mVars) `clearBit` v
      in if vIsRec then maybe generalise SubVar (head (bitSet2IntList partialRecCoocs)) else generalise

    -- (?) recmask to disallow merge x & A in (x & A) -> (µx.[Cons {%i32 , x}] & A)
    vPwP = polarCoocs True  ({-recMask .&.-} coocPVs) :: [VarSub]
    vMwM = polarCoocs False ({-recMask .&.-} coocMVs) :: [VarSub]
    -- look for some T present at all v+v- (since this is expensive and rarer try it last) `A & %i32 -> A & %i32`
    -- Note. THExt 1 <=> THPrim (PrimInt 32) are the same but fail here , so best avoid THExt as a dodgy optimisation
    vTs = let allCoocs = concat (pTs ++ mTs) in maybe generalise (\t -> SubTy (TyGround [t]))
      $ head =<< head (filter ((== length pTs + length mTs) . length) (group {-$ sort-} allCoocs))
      -- need to sort since group only joins adjacent elements (but that requires Ord on Types)
      -- TODO tycon Intersects eg. { a : t , b : _ } and { a : T } have a co-occurence { a : T }
--  intersectCooc :: [TyHead] -> [TyHead] -> [TyHead] = \t intersects -> let -- valid cooc intersections
--    intersectTH th intersect

    -- use foldl' to stop once we've found a reason to either Remove or Sub the tvar
    bestSub ok next = case ok of { Remove -> ok ;  SubTy _ -> ok ; SubVar _ -> ok ; _ko -> next }
    in foldl' bestSub (vPvM `bestSub` vPvMRec) (vPwP ++ vMwM) `bestSub` vTs

---------------------
-- tighten μ-types --
---------------------
-- There exists a few tricky cases:
-- | extract and merge μ-var co-occurences into outer binder
-- foldr1 : ∏ A B → (A → A → A) → µb.[Cons {A , µb.[Cons {⊤ , ⊤} | Nil]}] → A
--       => ∏ A B → (A → A → A) → µb.[Cons {A , b} | Nil] → A
-- | merge 2 equivalent μ-variables (a,b) while rolling 2 branches
-- rec1 v = { a = rec1 v , b = rec1 v }
--     ∏ A B → ⊤ → {a : µa.{a : a , b : µb.{a : a , b : b}} , b : µb.{a : µa.{a : a , b : b} , b : b}}
--  => ∏ A B → ⊤ → µa.{a : a , b : a}
-- | interleaved μs
-- flattenTree : ∏ A B C D → µb.[Node {A , µc.[Nil | Cons {b , c}]}] → µd.[Nil | Cons {A , d}]
-- This may need to know the polarity, for top/bot and to rm negative recursion
-- muBounds serves to propagate co-occurences of recursive vars upwards
type Roller = [THead (Maybe Type)] -- x to μx. binder [TypeF] typeconstructor wrappers
data TypeRoll
 = NoRoll    { forgetRoll' :: Type }
 | BuildRoll { forgetRoll' :: Type , mus :: NonEmpty (Int , Roller , Type) } -- μVar + tycon wrappers + bounds per mu
 | Rolling   { forgetRoll' :: Type , muR :: Int , roller :: Roller , resetRoll :: Roller }
 deriving Show
forgetRoll x = {-d_ (rollTy x)-} (forgetRoll' x)
-- forgetRoll but keeps μvar bounds
--dropRoll m = \case
--  BuildRoll uf ms -> mergeTypeList True $ uf : (filter (\(i,_,_) -> i `elem` m) (NE.toList ms) <&> \(_ , _ , t) -> t)
--  x -> forgetRoll x
--rollTy = \case
--  NoRoll{} -> "noroll"
--  BuildRoll{} -> "buildroll"
--  Rolling{} -> "rolling"

mergeTRolls :: [TypeRoll] -> TypeRoll
mergeTRolls = \case { x : xs -> foldr mergeRolls x xs ; [] -> _ }
mergeRollsNE :: NonEmpty TypeRoll -> TypeRoll
mergeRollsNE (x :| xs) = foldr mergeRolls x xs

-- substitute mu-bounds for another (merge recursive type vars)
patchMu :: Int -> Int -> Type -> Type
patchMu n m = let
  go = \case { THMuBound x | x == n -> THMuBound m ; THMu x t | x == n -> THMu m t ; x -> x }
  in cata $ \case
  TyGroundF g -> TyGround (go <$> g)
  TyVarsF v g -> TyVars v (go <$> g)
  x -> embed x

m_ = flip const-- d_
mergeRolls a b = -- d_ (rollTy a , rollTy b)
  (mergeRolls' a b)
mergeRolls' (NoRoll t) (NoRoll t2)       = NoRoll (mergeTypes True t t2) -- TODO pos/neg type merge?!
mergeRolls' (NoRoll _t) (BuildRoll a ms)  = BuildRoll (a {-mergeTypes True a t-}) ms
mergeRolls' (NoRoll _t) (Rolling a m r z) = Rolling   (a {-mergeTypes True a t-}) m r z
mergeRolls' a b@NoRoll{} = mergeRolls b a
mergeRolls' (Rolling a m r z) (Rolling a2 m2 _r2 _z2)
 | m == m2 = m_ ("roll-roll") $ Rolling (mergeTypes True a a2) m r z
 | m < m2  = m_ ("roll-roll" , m , m2) $ cata rollType (patchMu m2 m $ mergeTypes True a a2)
 | m > m2  = m_ ("roll-roll" , m , m2) $ cata rollType (patchMu m m2 $ mergeTypes True a2 a)

mergeRolls' (BuildRoll a ms) (BuildRoll a2 ms2) = m_ ("build-build" , fst3 <$> ms , fst3 <$> ms2) $
  BuildRoll (mergeTypes True a a2) (ms <> ms2)

mergeRolls' a@BuildRoll{} b@Rolling{} = mergeRolls b a
mergeRolls' (Rolling a m _r _z) (BuildRoll a2 ms)
 = m_ ("roll-build" , m , ms) $ let
   tbounds = NE.filter (\(n,_,_) -> n == m) ms <&> (\(_,_,b) -> b)
   in BuildRoll (mergeTypeList True (a : a2 : tbounds)) ms -- TODO merged roll + build somehow

rollType :: TypeF TypeRoll -> TypeRoll
rollType this = let -- ! we may be building | rolling μs out of multiple branches
  -- compute typeRolls from a single THead (each sub-branch of tycons).
  getTHeadTypeRoll :: Integer -> [Int] -> THead TypeRoll -> TypeRoll
  getTHeadTypeRoll vs ms th = let
    addMu m t@(TyGround [THMu n _]) = if n == m then t else error "internal error stacked μ"
    addMu m t = TyGround [THMu m t]
--  mkTy tt = if vs == 0 then TyGround [tt] else TyVars vs [tt]
    this = let tt = [forgetRoll <$> th] in if vs == 0 then TyGround tt else TyVars vs tt
    ith = Generalise.indexed th
    -- if. μ-bound in hole start μ-build
    -- if. Build in a hole => if μ-binder: switch build to roll ||| continue build
    -- if. Roll in hole check if roll ok: roll and reset ||| test more layers
    layer i = ith <&> \(j , t) -> if i == j then Nothing else Just (forgetRoll t) -- void out rec-branch for (==)
    -- TODO don't insert 'this' into rolls !! need to re-construct type at top to propagate μ-bounds
    -- 'this' is the current type, mkRoll examines each branch (one layer down)
    mkRoll :: Int -> TypeRoll -> [TypeRoll]
    mkRoll i = \case
      BuildRoll _ty mus -> [mergeRollsNE $ mus <&> \(m , rollFn , b) -> let l = layer i : rollFn
        in if m `elem` ms then let r = reverse l in Rolling (addMu m (mergeTypes True b this)) m r r
           else BuildRoll this ((m , l , b) :| [])]
      Rolling ty m (r : nextRolls) reset -> {-trace (prettyTyRaw ty <> " <=> " <> prettyTyRaw this)-} if layer i /= r -- TODO check subtype (roughly eq modulo μ and bounds)
        then [] -- NoRoll this
--      then NoRoll $ mkTy $ ith <&> \(j , oldT) -> if i == j then trace (prettyTyRaw ty) ty else forgetRoll oldT -- re-insert μ-bounds
        else [Rolling ty m (nextRolls <|> reset) reset]
      NoRoll _ -> []
      x -> error $ show x
    -- TODO use forget-roll properly, atm it mixes layers and is unreliable
    in case concat (Prelude.imap mkRoll (toList th)) of
      [] -> case ms of
        []  -> NoRoll this
        [m] -> BuildRoll (TyGround [THMuBound m]) ((m , [] , this) :| []) -- merge mu-bounds upwards
        _ -> _ -- merge μs build-build style
      x : xs -> foldr mergeRolls x xs

  -- Compute typeroll from a type merge
  aggregateBranches :: BitSet -> ([Int] , [THead TypeRoll]) -> TypeRoll
  aggregateBranches vs subs = let mkTy vs t = if vs == 0 then TyGround t else TyVars vs t
    in case subs of
    ([], xs) -> case getTHeadTypeRoll vs [] <$> xs of
      [] -> NoRoll (mkTy vs (fmap forgetRoll <$> xs))
      xs -> mergeTRolls xs
    (m , []) -> let allEq l = and (zipWith (==) l (drop 1 l)) in case m of
      mh:_ | allEq m -> BuildRoll (mkTy vs [THMuBound mh]) ((mh , [] , (TyGround [])) :| [])
      _   -> error (show m)
    (ms , xs) -> mergeTRolls (getTHeadTypeRoll vs ms <$> xs)
  partitionMus g = let (ms , gs) = Data.List.partition (\case {THMuBound{} -> True ; _ -> False}) g
    in (ms <&> (\(THMuBound m) -> m) , gs)
  in case this of
  TyVarsF vs g -> aggregateBranches vs (partitionMus g)
  TyGroundF g  -> aggregateBranches 0  (partitionMus g)
  _ -> NoRoll (embed $ fmap forgetRoll this)

deriving instance Show (THead (Maybe Type))
deriving instance Show (TyCon TypeRoll)
deriving instance Show (TyCon (Maybe Type))
deriving instance Show (THead TypeRoll)

-- Simplify + generalise TVars and add pi-binders
doGen :: V.Vector VarSub -> BitSet -> TypeF (Bool -> GEnv s Type) -> Bool -> GEnv s Type
doGen tvarSubs recs rawType pos = let
  generaliseVar :: Int -> GEnv s Int -- A..Z names for generalised typevars
  generaliseVar v = use genMap >>= \mp -> MV.read mp v >>= \perm -> if perm /= complement 0 then pure perm else do
    q <- quants <<%= (1+)
    q <$ MV.write mp v q <* when debug_gen (traceM $ show v <> " => ∀" <> toS (number2CapLetter q))

  genVar :: Int -> GEnv s Type
  genVar v = if v >= V.length tvarSubs
    then generaliseVar v <&> \q -> TyGround [if testBit recs v then THMuBound q else THBound q] 
    else case tvarSubs V.! v of
    Escaped    -> pure (TyVars (setBit 0 v) [])
    Remove     -> pure (TyGround []) -- pure $ if leaks `testBit` v then TyVar v else TyGround []
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
  registerOccurs :: Bool -> Type -> AnaEnv s Type
  registerOccurs pos ty = {-trace (prettyTyRaw ty) $-} use coocs >>= \cooc -> partitionType ty & \(vset , _tys) ->
    ty <$ (bitSet2IntList vset) `forM` \i ->
--    MV.modify cooc (over (if pos then _1 else _2) (TyVars vset other :)) i
      MV.modify cooc (over (if pos then _1 else _2) (\l -> if elem ty l then l else ty : l)) i
      -- TODO co-occurence directly

  subVar pos loops guarded v = if
    | testBit loops v   -> pure (TyVars loops []) -- unguarded var loop
    | testBit guarded v -> TyVars (0 `setBit` v) [] <$ (recs %= (`setBit` v))
    | otherwise -> use anaBis >>= \b -> use instVars >>= \iv -> if v >= iv
      then pure $ TyVars (setBit 0 v) [] -- THBound vars spawned in later
      else MV.read b v >>= \(BiSub pty mty) -> let -- not atm a TVar cycle
      loops' = setBit loops v
      ty = if pos then pty else mty
      in if nullType ty then pure (TyVars loops' [])
        else mergeTVar v <$> analyseType ty pos loops' guarded

  go :: [THead (Acc s)] -> BitSet -> Acc s
  go g vars pos loops guarded = let
    varSubs = bitSet2IntList vars `forM` subVar pos loops guarded
    mkT t = TyGround [t]
    grounds :: [THead (Acc s)] -> AnaEnv s [Type] -- GroundType
    grounds g = let loops' = 0 ; guarded' = guarded .|. loops .|. vars in g `forM` \case
      tycon@(THTyCon t) -> fmap mkT $ case t of -- update loops and guarded for tycons
     -- THArrow is the only tycon with contravariant subtrees
        THArrow ars r -> fmap THTyCon $ THArrow
          <$> traverse (\arg -> registerOccurs (not pos) =<< arg (not pos) loops' guarded') ars
          <*> (registerOccurs pos =<< r pos loops' guarded')
        _ -> traverse (\x -> registerOccurs pos =<< x pos loops' guarded') tycon

      -- THBounds cannot occur together with tvars, else would have been instantiated already
      THBound b   -> use instVars >>= \vn -> subVar pos loops guarded (vn + b)
      THMuBound m -> use instVars >>= \vn -> subVar pos loops guarded (vn + m)
      THBi _b ty  -> {-(instVars <<%= (b+)) *>-} ty pos loops guarded -- TODO stacked THBis?
      THMu m ty -> use instVars >>= \vn ->
        (recs %= (`setBit` (vn + m))) *> ty pos loops guarded <&> mergeTVar (vn + m)
      x -> mkT <$> traverse (\x -> x pos loops guarded) x
    in (\grounds vs -> mergeTypeList pos (grounds ++ vs)) <$> grounds g <*> varSubs

  in cata $ \t pos loops guarded -> case t of
    TyGroundF g  -> go g 0  pos loops guarded
    TyVarsF vs g -> go g vs pos loops guarded
    x -> embed <$> traverse (\x -> x pos loops guarded) x

{-
-- recursively sub-in all type vars and build co-occurence vector
-- TODO instvars needs to be monadic
analyse :: forall s. MV.MVector s BiSub -> Seed -> AEnv s (TypeF Seed)
analyse bis seed@(ty , pos , loops , guarded , instVars) = let
  go :: [TyHead] -> BitSet -> AEnv s (TypeF Seed)
  go g vars = let
    registerOccurs :: Bool -> Type -> AEnv s Type
    registerOccurs pos ty = {-trace (prettyTyRaw ty) $-} use acoocs >>= \cooc -> partitionType ty & \(vset , other) ->
      ty <$ bitSet2IntList vset `forM` \i ->
        MV.modify cooc (over (if pos then _1 else _2) (\l -> if elem ty l then l else ty : l)) i

    varSubs = bitSet2IntList vars `forM` subVar instVars
    mkT t = TyGroundF [THTyCon t]
    grounds :: [TyHead] -> AEnv s [TypeF Seed]
    grounds g = let loops' = 0 ; guarded' = guarded .|. loops .|. vars in g `forM` \case
      tycon@(THTyCon t) -> fmap mkT $ case t of -- update loops and guarded for tycons
        THArrow ars r -> THArrow -- THArrow is the only tycon with contravariant subtrees
          <$> (traverse (registerOccurs (not pos)) ars <&> fmap (, not pos , loops' , guarded' , instVars))
          <*> (registerOccurs pos r <&> (, pos , loops' , guarded' , instVars))
        _ -> traverse (registerOccurs pos) t <&> fmap (, pos , loops' , guarded' , instVars)

      -- THBounds cannot occur together with tvars, else would have been instantiated already
      THBound b   -> subVar instVars (instVars + b)
      THMuBound m -> subVar instVars (instVars + m)
      THBi b ty   -> pure (fmap (, pos , loops , guarded , instVars + b) (project ty))
      THMu m ty -> (arecs %= (`setBit` (instVars + m)))
        $> (fmap (, pos , loops, guarded , instVars + m) . project) (mergeTVar (instVars + m) ty)
      x -> pure $ TyGroundF [(fmap (, pos , loops , guarded , instVars) x)]
    in (\grounds vs -> mergeTypeFList pos (grounds ++ vs)) <$> grounds g <*> varSubs

  subVar :: Int -> Int -> AEnv s (TypeF Seed)
  subVar instVars' v = if
    | testBit loops v   -> pure (TyVarsF loops []) -- unguarded var loop
    | testBit guarded v -> TyVarsF (0 `setBit` v) [] <$ (arecs %= (`setBit` v)) -- recursive tvar
    | v >= instVars'    -> pure (TyVarF v) -- THBound vars spawned in later (?!)
    | otherwise -> MV.read bis v >>= \(BiSub pty mty) -> let -- not atm a TVar cycle
      loops' = setBit loops v
      ty = if pos then pty else mty
      in if nullType ty then pure (TyVarsF loops' [])
         else mergeTypeF (TyVarF v) <$> analyse bis (ty , pos , loops' , guarded , instVars') -- HACK merge tvar !
  in case ty of
  TyGround g  -> go g 0
  TyVars vs g -> go g vs
  TyVar v     -> subVar instVars v
  x -> _ -- project <$>

analyseT :: MV.MVector s BiSub -> Seed -> AEnv s Type
analyseT bis = anaM (analyse bis)

mergeTypeF (TyGroundF a) (TyGroundF b) = TyGroundF (a ++ b)
mergeTypeFList _pos = foldr mergeTypeF (TyGroundF [])
-}
