-- Biunfication records constraints , generalisation makes sense of them
module Generalise (generalise) where
import CoreSyn
import CoreUtils
import PrettyCore
import TCState
import BiUnify (instantiate)
import Control.Lens
import Data.List (partition)
import qualified Data.Vector.Mutable as MV
import qualified Data.Text as T

-- Generalisation quantifies over only local tvars of a type T
-- generalising tvars that escape into enclosing scope would allow them to be instantiated to anything
-- escapedVars : BitSet indicates which tvars escape and should be left alone
-- thus most let-bindings have to be generalised twice
--  1. if locally used more than once they need to be instantiatable (else can skip and inline it)
--  2. finally fully generalise it once its freevars have been generalised at enclosing scope
-- * f1 x = let y z = z in y   -- nothing can go wrong
-- * f2 x = let y   = x in y   -- if x generalised at y => f2 : a -> b
-- * f3 x = let y y = x y in y -- similar

-- Simplifications:
--  * ? A -> A & Int =? Int -> Int
--  * remove polar variables `a&int -> int` => int->int ; `int -> a` => `int -> bot`
--  * unify inseparable variables (co-occurence `a&b -> a|b` and indistinguishables `a->b->a|b`)
--  * remove variables that contain the same upper and lower bound (a<:t and t<:a)`a&int->a|int`
--  * tighten recursive types

-- eg. foldr : (A → (C & B) → B) → C → μx.[Cons : {A , x} | Nil : {}] → (B & C)
-- =>  foldr : (A → B → B) → B → μx.[Cons : {A , x} | Nil : {}] → B

-- Generalisation is a 2 pass process
-- 1. Preparation & Analysis:
--   * read TVar bounds from Bisubs
--   * detect tvar cycles and whether they are guarded by TyCon (loops and recVars BitSets)
--   * hash consing (merge type constructors to bring TVars closer together)
--   * save TVar co-occurences
-- 2. Finalise:
--   * Remove or generalise TVars (depending on co-occurence)
--   * insert and tighten recursive types
generalise :: BitSet -> IName -> TCEnv s Type
generalise escapees recTVar = let
  showTys t        = T.intercalate " , " (prettyTyRaw <$> t)
  traceCoocs occLen coocs = [0..occLen -1] `forM_` \i -> MV.read coocs i >>= \(p,m) ->
    traceM (show i <> ": + [" <> showTys p <> " ]; - [" <> showTys m <> "]")
  in do
  when global_debug (traceM $ "Gen: " <> show recTVar)
  (quants .= 0)

  bs <- use bis
  let coocLen = MV.length bs + 5 -- + let-bound instantiatables
  (biEqui .=)   =<<  MV.replicate coocLen (complement 0)
  (coOccurs .=) =<< MV.replicate coocLen ([],[])
  recVars .= 0

  analysed <- substTypeVar True recTVar 0 0
  recursives <- use recVars
  occurs <- use coOccurs
  occLen <- use blen
  when global_debug (traceCoocs occLen occurs)

  polars <- let -- Remove non-recursive typevars that occur only at one polarity (trivial case of co-occurence)
    testPolar polars i = MV.read occurs i >>= \(a,b) ->
      if not (escapees `testBit` i) && (null a || null b) && not (recursives `testBit` i)
      then setBit polars i <$ MV.write occurs i ([],[]) else pure polars
    in foldM testPolar (0 :: BitSet) [0..occLen - 1]

  -- co-occurence analysis
  unifiables  <- let
    getTVars = (\(a,b) -> ((\case {THVars vs->vs} <$> a),b)) . partition (\case {THVars{}->True ; _ -> False })

    -- hasCooc t1 t2: find tvars that always cooccur with some T in both t1 and t2
    -- hoping to unify them with T (remove the co-occuring tvars)
    -- unifying recursive and non-recursive vars is only admissible if the non-rec var is also covariant
    hasCooc v t1 t2 = let
      ((pTVs , p) , (mTVs , m)) = (unzip (getTVars <$> t1) , unzip (getTVars <$> t2)) -- :: (([[BitSet]], [[TyHead]]) , _)
      coocVs = (foldr (.|.) 0 (concat pTVs) .|. foldr (.|.) 0 (concat mTVs)) -- `clearBit` v
      recCoocs = coocVs .&. recursives -- TODO iff the non-rec vars are covariant (strictly polar)
      coocL' = bitSet2IntList coocVs
      lvs    = fromMaybe v (head (bitSet2IntList recCoocs) <|> head coocL') -- last var standing
      unified = setBit 0 lvs
      mergeCoocs occs = [foldr mergeTypes [] occs] -- dubious..?
      in if coocVs == 0
         then {- if some Type is present in all p and in all m then unify v with it (rm v) -} Nothing
         else Just ([] , (mergeCoocs $ (THVars unified :) <$> p , mergeCoocs $ (THVars unified :) <$> m))

    testCoocs voids v = if testBit voids v || testBit escapees v then pure voids else
      MV.read occurs v >>= \(pRaw , mRaw) -> do
        -- indistinguishables: v + T always occur together at +v,-v => drop v (unify with T)
        voids1 <- case hasCooc v pRaw mRaw of
          Just (drops , occ') -> setBit voids v <$ (MV.write occurs v occ') -- *> drops `forM` \i -> MV.write occurs i occ')
          Nothing             -> pure voids
        -- polarEquality:      v + w always occur together at +v,+w or at -v,-w => drop v (unify with w)
        MV.read occurs v >>= \(pRaw , mRaw) -> let
          testPolarCooc pos v voids t = case t of
            [[THVars vs]] -> let -- Right is used to terminate the foldM once a cooc is found
               go (Right voids) i = pure (Right voids)
               go (Left voids)  i = MV.read occurs i <&> (if pos then fst else snd) <&> hasCooc v t >>= \case
                Just (drops , occ') -> Right (setBit voids i) <$ MV.write occurs v occ'
                Nothing      -> pure $ Left voids
              in foldM go (Left voids) (bitSet2IntList (clearBit vs v)) <&> \case { Right v -> v ; Left v -> v }
            _ -> pure voids
          in testPolarCooc True  v voids1 pRaw >>= \voids2 -> testPolarCooc False v voids2 mRaw
    in foldM testCoocs polars [0..occLen - 1]

  coOccurs .= occurs

  when global_debug $ do
    traceM $ "analysed: "   <> prettyTyRaw analysed
    traceM $ "escapees: "   <> show (bitSet2IntList escapees)
    traceM $ "unifiables: " <> show (bitSet2IntList unifiables)
    traceM $ "recVars: "    <> show (bitSet2IntList recursives)
    use coOccurs >>= traceCoocs occLen
  subGen escapees unifiables recursives analysed

rmTVar v = fmap $ \case
  THVars vs -> THVars (vs `clearBit` v)
  x -> x

latticeTop pos = \case
  [] -> [if pos then THBot else THTop] -- pure ty
  t  -> t

-- Final step; eliminate all THVars
-- * either sub in THBound | unify with co-occurences (possibly [])
subGen :: BitSet -> BitSet -> BitSet -> Type -> TCEnv s Type
subGen escapedVars unifiables recursives raw = use bis >>= \b -> use biEqui >>= \biEqui' -> use coOccurs >>= \coocs ->
  latticeTop True <$> let
  generaliseVar v = MV.read biEqui' v >>= \perm ->
    if perm /= complement 0 then pure perm
    else do
      q <- quants <<%= (+1)
      when global_debug (traceM $ show v <> " =>∀ " <> toS (number2CapLetter q))
      q <$ MV.write biEqui' v q
  doVar pos v = if
    | escapedVars `testBit` v -> pure [THVars (0 `setBit` v)]
    | recursives  `testBit` v -> MV.read coocs v >>= \(p' , m') -> let (p , m) = (rmTVar v <$> p' , rmTVar v <$> m')
      in case if pos then (p,m) else (m,p) of
      ([] , []) -> generaliseVar v <&> \q -> [THBound q] -- [THMuBound 0]
      (t , _ {-[]-}) -> do
        MV.write coocs v ([],[])
        raw <- goJoin pos $ rmTVar v (foldr mergeTypes [] t)
        q   <- generaliseVar v <&> \q -> THBound q
        pure (q : raw) -- pure [THMu 0 raw]
--    t -> error $ "Recursive var is not strictly covariant! " <> show (pos , p , m)
    | unifiables `testBit` v -> MV.read coocs v >>= \(p , m) -> case if pos then p else m of
      -- substitute a TVar for its co-occurence , generalise if still present after substitution
      []  -> pure []
      [t] -> if any (\case { THVars vs -> testBit vs v ; _ -> False } ) t
             then (\q t -> THBound q : t) <$> generaliseVar v <*> goJoin pos (rmTVar v t)
             else goJoin pos t
      t   -> error $ "Multiple cooccurence substitutions" <> show t
    | True -> generaliseVar v <&> \q -> [THBound q]

  goJoin pos ty = fmap (foldr mergeTypes []) (mapM (finaliseTyHead pos) ty)
  finaliseTyHead pos = \case
    THVars v  -> foldr mergeTypes [] <$> (doVar pos `mapM` bitSet2IntList v)
    THVar v   -> doVar pos v
    x -> (\x -> [x]) <$> case x of
      THBi b ty -> THBi b <$> goJoin pos ty
      THMu x ty -> THMu x <$> goJoin pos ty
      THTyCon t -> let goGuarded pos = fmap (latticeTop pos) . goJoin pos in THTyCon <$> case t of
        THArrow ars r -> THArrow   <$> traverse (goGuarded (not pos)) ars <*> goGuarded pos r
        THProduct   r -> THProduct <$> traverse (goGuarded       pos) r
        THSumTy     r -> THSumTy   <$> traverse (goGuarded       pos) r
        THTuple     r -> THTuple   <$> traverse (goGuarded       pos) r
      x -> pure x
  in goJoin True raw >>= \done -> use quants <&> \q -> if q > 0 then [THBi q done] else done

-- Read typevars from Bisubs, collect co-occurences and identify recursive types
-- non-escaped typevars are possibly safe to cache their substitution to (=<< updateVar)
substTypeVar pos v loops guarded = use bis >>= \b -> if
  | testBit loops v   -> pure [THVars loops] -- unguarded var loop
  | testBit guarded v -> [THVars (0 `setBit` v)] <$ (recVars %= (`setBit` v))
  | otherwise -> MV.read b v >>= \(BiSub pty mty) -> let -- not atm a TVar cycle
    loops'    = setBit loops v
    in case (if pos then pty else mty) of
      [] -> pure [THVars loops']
      ty -> substTypeMerge pos loops' guarded ty

-- typevars need to know what they co-occur with, for simplification purposes
registerOccurs :: Bool -> Type -> TCEnv s Type
registerOccurs pos ty = use coOccurs >>= \cooc -> let
  (vars , other)    = partition ((== KVars) . kindOf) $ ty
  vset              = foldr (.|.) 0 $ (\(THVars v) -> v) <$> vars
  mkTy vset i other = THVars vset : other -- leave the var itself in the vset
  in ty <$ bitSet2IntList vset `forM` \i ->
    MV.modify cooc (over (if pos then _1 else _2) (mkTy vset i other :)) i

substTypeMerge :: Bool -> Integer -> Integer -> Type -> TCEnv s Type
substTypeMerge pos loops guarded ty =  let
  (tvarsRaw , others) = partition (\case { THVars{}->True;THVar{}->True;_->False}) ty
  tvars = foldr (.|.) 0 (\case { THVars v -> v ; THVar i -> setBit 0 i } <$> tvarsRaw)
  guarded' = guarded .|. loops .|. tvars
  substTyHead = let
    substGuarded p t = registerOccurs p =<< (mergeTypes [] <$> substTypeMerge p 0 guarded' t)
    in \case
    THTyCon t -> (\x -> [THTyCon x]) <$> case t of
      THArrow ars r -> THArrow   <$> traverse (substGuarded (not pos)) ars
                                 <*> substGuarded pos r
      THProduct   r -> THProduct <$> traverse (substGuarded pos) r
      THSumTy     r -> THSumTy   <$> traverse (substGuarded pos) r
      THTuple     r -> THTuple   <$> traverse (substGuarded pos) r
    t@THPrim{} -> pure [t]
    t@THExt{} -> pure [t]
    t@THTop{} -> pure [t]
    t@THBot{} -> pure [t]
    THBi n t  -> do
      r <- instantiate n t >>= substGuarded pos -- a generalised let-bound function
      pure r
--  t@THMu{}  -> pure [t]
    x -> error $ show x --pure [x]
  in do
    vs <- bitSet2IntList tvars `forM` \x ->
      (THVars (setBit 0 x) :) <$> substTypeVar pos x loops guarded
    ts <- substTyHead `mapM` others
    pure (foldr mergeTypes [] (vs ++ ts))
