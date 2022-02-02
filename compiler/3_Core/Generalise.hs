-- Biunfication only records type bounds
-- At|during generalisation substitute all type variables
module Generalise (generalise) where
import CoreSyn
import CoreUtils
import PrettyCore
import TypeCheck
import TCState
import Control.Lens
import Data.List (partition)
import qualified Data.IntMap as IM
import qualified Data.Vector.Mutable as MV
import qualified Data.Text as T

-- Generalization (Gen G t) quantifies over only free tvars of t that do not occur in G
-- Otherwise if they escape into enclosing scope they can be instantiated to anything
-- Thus escapedVars indicate which tvars escape and mustn't be touched
-- let-bindings 'have' to be generalised twice
--  1. if locally used more than once they need to be instantiatable (else can skip, though will have monomorphic type then)
--  2. finaly fully generalise it once its freevars have been figured out
-- * f1 x = let y z = z in y   -- nothing can go wrong
-- * f2 x = let y   = x in y   -- typeof x quantified too early => f2 : a -> b
-- * f3 x = let y y = x y in y -- similar

-- Simplifications:
--  * ? A -> A & Int =? Int -> Int
--  * remove polar variables `a&int -> int` => int->int ; `int -> a` => `int -> bot`
--  * unify inseparable variables (co-occurence `a&b -> a|b` and indistinguishables `a->b->a|b`)
--  * remove variables that contain the same upper and lower bound (a<:t and t<:a)`a&int->a|int`
--  * roll up recursive types

-- * substitute tvars for ground types or recursive types when possible
-- * Rec|Mu: A Typevar occuring both above and below a type constructor
-- * else mark tvars for generalisation (pending their survival of simplification)
-- * prepare for subGen (count gened TVar occurrences etc..)

-- Co-occurence analysis: If a typevar always occurs positively (or negatively) with T
--  , it can be unified with T (~ removed)
-- eg. foldr : (A → (C & B) → B) → C → μx.[Cons : {A , x} | Nil : {}] → (B & C)
--     foldr : (A → B → B) → B → μx.[Cons : {A , x} | Nil : {}] → B

-- Generalisation is a 2 pass process
-- 1. Preparation & Analysis:
--   * inline TVar bounds read from Bisubs
--   * detect cycles using 2 BitSets (mark recursive types if guarded by Tycon)
--   * hash consing (merge type constructors to bring TVars closer together)
--   * save TVar co-occurences
-- 2. Finalise: Remove or generalise TVars (depending on co-occurence)
generalise :: IName -> TCEnv s Type
generalise recTVar = let
  showTys t        = T.intercalate " , " (prettyTyRaw <$> t)
  traceCoocs coocs = [0..MV.length coocs -1] `forM_` \i -> MV.read coocs i >>= \(p,m) ->
    traceM (show i <> ": + [" <> showTys p <> " ]; - [" <> showTys m <> "]")
  in do
  when global_debug (traceM $ "Gen: " <> show recTVar)
  (quants .= 0) *> (mus .= 0)

  liftMu .= Nothing
  bs <- use bis
  b  <- MV.replicate (MV.length bs) (complement 0)
  biEqui .= b
  (coOccurs .=) =<< MV.replicate (MV.length bs) ([],[])

  analysed <- substTypeVar True recTVar 0 0
  when global_debug (use coOccurs >>= traceCoocs)

  escaped <- use escapedVars
  occurs <- use coOccurs
  polars <- let -- bitmask for polar TVars
    go polars i = MV.read occurs i >>= \(a,b) ->
      if not (escaped `testBit` i) && (null a || null b)
      then (polars `setBit` i) <$ MV.write occurs i ([],[])
      else pure polars
    in foldM go (0 :: Integer) [0..MV.length occurs - 1]

  voidedTVars  <- let -- bitmask for all tvars that can be dropped (polars + co-occurs)
    mergeOccs = let -- a cooccurrence is a list of types co-occuring with this var
      domerge [THVars i] (Just [THVars j]) = let
        (a,b) = (i .&. complement polars , j .&. complement polars) -- rm polar tvars
        in if a == b then Just [THVars a] else Nothing
      domerge t1 t2 = Nothing
      in \x -> case x of
        [t]     -> Just t
        (t1:tn) -> foldr domerge (Just t1) tn
        _       -> Nothing

    -- cooccurs: if a alway occurs pos (resp. neg) with b AND vice-versa, they can be unified
    cooc pos c voids t = case {- d_ (c , t) $-} t of --did_ t of
      Just [THVars v] -> (bitSet2IntList (clearBit v c) `forM` \i ->
        (MV.read occurs i <&> (if pos then fst else snd))
        ) <&> map mergeOccs <&> catMaybes >>= \case
          [] -> pure voids
          (a : alts) -> let
            eqTyHead (THVars a) (THVars b) = b == a --(a .&. b) == a -- b == a
            eqTys (a:ax) (b:bx) = eqTyHead a b && eqTys ax bx -- TODO permutations?
            eqTys _ _ = False
            tvars@(first : _) = bitSet2IntList v
            unified = [THVars (0 `setBit` first)]
            in if c /= first && all (eqTys [THVars v]) alts -- || not (testBit v c)
               then let voids' = voids `setBit` c in do
                 tvars `forM` \i -> MV.write occurs i $ {-d_ (c , unified)-} ([unified] , [unified])
                 -- if we managed to simplify earlier vars, try again since they are likely further simplifiable
                 foldM go voids' (bitSet2IntList (v .&. setNBits (c - 1)))
               else pure voids
      _ -> pure voids
    go voids i = if testBit voids i || testBit escaped i then pure voids else

      -- indistinguishables: if a + b always occur together at both polarities, they can be unified
      MV.read occurs i >>= \(pRaw@(x:xs) , mRaw) -> let others = pRaw ++ mRaw in case x of
        [THVars v] -> let (a:as) = (\case { [THVars v] -> v ; _ -> 0 }) <$> others
                          co = foldr (.&.) a as `clearBit` i
                          tvars@(first : _) = bitSet2IntList co
                          sub = [[THVars co]]
--                        sub = if clearBit co i == 0 then [[]] else [[THVars co]]
          in if co == 0 then pure voids else let voids' = setBit voids i in do
            MV.write occurs i (sub , sub)
            pure voids'
--          foldM go voids' (bitSet2IntList (v .&. setNBits (i - 1)))
        t        -> pure voids -- TODO check if t occurs everywhere

      -- cooccurs: if a alway occurs pos (resp. neg) with b AND vice-versa, they can be unified
      >>= \voids -> MV.read occurs i >>= \(pRaw , mRaw) -> let (p , m) = (mergeOccs pRaw , mergeOccs mRaw)
      in    cooc True  i voids  p >>= \voids' -> if testBit voids' i then pure voids'
      else  cooc False i voids' m
    in foldM go polars [0..MV.length occurs - 1]
  coOccurs .= occurs

  when global_debug $ do
    traceM $ "analysed: " <> prettyTyRaw analysed
    traceM $ "voids: "    <> show (bitSet2IntList voidedTVars)
    traceM $ "escaped: "  <> show (bitSet2IntList escaped)
    use coOccurs >>= traceCoocs
  subGen escaped voidedTVars analysed

-- Final step; eliminate all THVars
-- * either sub in THBound | unify with co-occurences (possibly [])
subGen :: Integer -> Integer -> Type -> TCEnv s Type
subGen escapedVars voids raw = use bis >>= \b -> use biEqui >>= \biEqui' -> use coOccurs >>= \cooc ->let
  generaliseVar v = MV.read biEqui' v >>= \perm ->
    if perm /= complement 0 then pure perm
    else do
      q <- quants <<%= (+1)
      when global_debug (traceM $ show v <> " => ∀" <> show q)
      q <$ MV.write biEqui' v q
  doVar pos v = if escapedVars `testBit` v then pure [THVars (0 `setBit` v)] else -- cannot generalise captured tvars
    if voids `testBit` v
    -- substitute a TVar for its co-occurence
    then use coOccurs >>= \coocs -> MV.read coocs v <&> (if pos then fst else snd) >>= \case
      []  -> pure []
--    [t] -> pure t
      [t] -> goJoin pos t
--    [[THVars vs]] -> goJoin pos [THVars $ vs `clearBit` v]
      t   -> error $ "Multiple cooccurence substitutions" <> show t
    else generaliseVar v <&> \q -> [THBound q]

  goJoin pos ty = fmap (foldr mergeTypes []) (mapM (finaliseTyHead pos) ty) >>= \case
    [] -> pure [if pos then THBot else THTop] -- pure ty
    t  -> pure t
  finaliseTyHead pos = \case
    THVars v  -> foldr mergeTypes [] <$> (doVar pos `mapM` bitSet2IntList v)
    THVar v   -> doVar pos v
    x -> (\x -> [x]) <$> case x of
      THBi b ty -> THBi b <$> goJoin pos ty
      THMu x ty -> THMu x <$> goJoin pos ty
      THTyCon t -> THTyCon <$> case t of
        THArrow ars r -> THArrow   <$> traverse (goJoin (not pos)) ars <*> goJoin pos r
        THProduct   r -> THProduct <$> traverse (goJoin       pos) r
        THSumTy     r -> THSumTy   <$> traverse (goJoin       pos) r
        THTuple     r -> THTuple   <$> traverse (goJoin       pos) r
      x -> pure x
  in goJoin True raw >>= \done -> use quants <&> \q -> if q > 0 then [THBi q done] else done

-- Read typevars from Bisubs, collect co-occurences and identify recursive types
-- non-escaped typevars are locally ours so possibly safe to cache its substitution to (=<< updateVar)
-- TODO don't add mu if contravariantly recursive
substTypeVar pos v loops guarded = use bis >>= \b ->
  if testBit loops v
  then pure [THVars loops]
  else if testBit guarded v -- recursive type
    then mus <<%= (+1) >>= \m -> [THMuBound m] <$ (muEqui %= (IM.insert v m))
    else MV.read b v >>= \(BiSub pty mty) -> let -- not (yet) a TVar cycle
      loops'    = setBit loops v
      loopsList = bitSet2IntList loops'
      in case (if pos then pty else mty) of
      [] -> pure [THVars loops]
      ty -> do
        rawT <- substTypeMerge pos loops' guarded ty
        mus .= 0
        musCur <- muEqui <<%= (\m -> foldr IM.delete m loopsList)
        mergeTypes [] <$> let addMu t = maybe (pure t) (addMuBind rawT t)
          in foldM addMu rawT ((musCur IM.!?) <$> loopsList)

-- typevars need to know what they co-occur with, for simplification purposes
registerOccurs :: Bool -> Type -> TCEnv s Type
registerOccurs pos ty = use coOccurs >>= \cooc -> let
  (vars , other) = partition ((== KVars) . kindOf) $ ty
  vset              = foldr (.|.) 0 $ (\(THVars v) -> v) <$> vars
  mkTy vset i other = THVars vset : other -- leave the var itself in the vset
  in ty <$ bitSet2IntList vset `forM` \i -> MV.modify cooc (over (if pos then _1 else _2) (mkTy vset i other :)) i

substTypeMerge :: Bool -> Integer -> Integer -> Type -> TCEnv s Type
substTypeMerge pos loops guarded ty = fmap (foldr mergeTypes []) $ ty `forM` let
  substGuarded p t = (registerOccurs p =<<) $ (mergeTypes []) <$> substTypeMerge p 0 (guarded .|. loops) t
  in \case
  THVar x   -> (THVars (setBit 0 x) :) <$> substTypeVar pos x loops guarded
  THBi b ty -> (\t->[THBi b t])   <$> substGuarded pos ty
  THMu x ty -> insertMu x <$> substGuarded pos ty
  THTyCon t -> let
      hashCons t = use liftMu <&> \case
        Just mt | check _ mempty mempty [THTyCon t] mt -> mt
        _ -> [THTyCon t]
    in hashCons =<< case t of
    THArrow ars r -> THArrow   <$> traverse (substGuarded (not pos)) ars <*> substGuarded pos r
    THProduct   r -> THProduct <$> traverse (substGuarded pos) r
    THSumTy     r -> THSumTy   <$> traverse (substGuarded pos) r
    THTuple     r -> THTuple   <$> traverse (substGuarded pos) r
  x -> pure [x]

insertMu x t = let
  -- Note. [y & µx._] means y and x are the same recursive type
  -- µx.µy. = µx. ; y and x are the same
  rmMuBound x = filter (\case { THMuBound y -> False ; _ -> True })
  rmOuterMus x t = case t of
    THMu y t -> let (xs , ts) = unzip $ rmOuterMus x <$> t in (min y (minimum xs) , concat ts)
    t        -> (x , [t])
  (x' , t') = unzip $ rmOuterMus x <$> rmMuBound x t
  in [THMu (minimum x') (concat t')]

addMuBind rawT guarded x = do
  let (mTypes , other) = partition (\case { THMuBound i->True ; _->False }) rawT
      mbound = (\(THMuBound i) -> i) <$> mTypes
  mn <- muNest <<%= (IM.union (IM.fromList $ ( , (x , other)) <$> mbound))
  r <- case mn IM.!? x of -- can we replace t with subT (a tighter recursive type)
    Just (y , subT) | True <- check _ mempty mempty other subT -> pure (insertMu y subT)-- [THMu y subT]
    _ -> pure (insertMu x guarded)-- [THMu x guarded]
  liftMu .= (Just r)
  pure r
