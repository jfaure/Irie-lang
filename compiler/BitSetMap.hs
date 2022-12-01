{-# LANGUAGE DeriveDataTypeable , DeriveFoldable , DeriveTraversable , GeneralizedNewtypeDeriving , InstanceSigs #-}
-- product | sumtype keys are static lists usually consisting of many neighboring bounded integers
-- insertion is O(n), but all other operations are more space efficient and faster than IntMap
-- fromList O(n)
-- (!?) O(1)
-- union , intersection , mergeWithKey O(n)
module BitSetMap (BitSetMap , size , fromList , fromListWith , BitSetMap.toList , foldrWithKey , singleton , (!?) , BitSetMap.elems , BitSetMap.keys
  , unionWith , intersectionWith , traverseWithKey , mergeWithKey' , mergeWithKey , mapAccum , mapWithKey) where

-- For oneshot built ordered lists, dichotomy lookup on a (Vector (Int , a)) is a clear improvement vs Data.IntMap
import Data.Binary ( Binary )
import Data.Vector.Binary ()
import qualified Data.Traversable as DT ( mapAccumL )
import qualified Data.Vector as V ( Vector, (!), fromList, length, map, singleton, toList, unfoldrN )

newtype BitSetMap a = BSM { unBSM ∷ V.Vector (Int , a) }
  deriving (Eq , Generic , Show)
instance (Binary e) ⇒ Binary (BitSetMap e)
--instance Semialign BitSetMap where
--  alignWith f = mergeWithKey (\k a b → f (These a b)) (\k x → f (This x)) (\k y → f (That y))
instance Functor BitSetMap where
  fmap f = BSM . fmap (\(a , b) → (a , f b)) . unBSM
instance Foldable BitSetMap where
  foldr ∷ (a → b → b) → b → BitSetMap a → b
  foldr f z = foldr (\(_ , v) acc → f v acc) z . unBSM
instance Traversable BitSetMap where
  traverse f = fmap BSM . traverse (\(a,b) → (a,) <$> f b) . unBSM

size       = V.length . unBSM
toList   l = V.toList (unBSM l)
fromList l = BSM (V.fromList (sortOn fst l))
--fromVec  l = BSM (V.sortOn fst l)

fromListWith ∷ (b → b → b) → [(Int , b)] → BitSetMap b
fromListWith f l = let
  combine (a : b : l) = if ((==) `on` fst) a b then combine ((fst a , (f `on` snd) a b) : l) else a : combine (b : l)
  combine l = l
  in BSM $ V.fromList (combine (sortOn fst l))

read = \(BSM v) i → v V.! binarySearch v i 0 (V.length v - 1)
(!?) = \v i → let r = read v i in if fst r == i then Just (snd r) else Nothing

binarySearch ∷ V.Vector (Int , a) → Int → Int → Int → Int
binarySearch = \v e → let
  -- dichotomy in [l,u) (start at 0 (length vec))
  loop l u = if u <= l then l else let k = (u + l) `div` 2 in case compare (fst (v V.! k)) e of
    EQ -> k
    LT -> loop (k + 1) u
    GT -> loop l k
  in loop

elems = fmap snd . unBSM
keys  = fmap fst . unBSM

mapAccum ∷ (a → b → (a, c)) → a → BitSetMap b → (a, BitSetMap c)
mapAccum f seed bsm = let
  accFn acc (i , v) = let (next , c) = f acc v in (next , (i , c))
  (r , v) = DT.mapAccumL accFn seed (unBSM bsm)
  in (r , BSM v)

mapWithKey ∷ (Int → v → b) → BitSetMap v → BitSetMap b
mapWithKey f = BSM . V.map (\(l , v) → (l , f l v)) . unBSM

traverseWithKey f = fmap BSM <$> traverse (\(l , v) → (l ,) <$> f l v) . unBSM

--unionWith ∷ (a → a → a) → BitSetMap a → BitSetMap a → BitSetMap a
unionWith f (BSM a) (BSM b) = let
  go (i , j) | i >= V.length a && j >= V.length b = Nothing
  go (i , j) | i >= V.length a = Just (b V.! j , (i     , j + 1))
  go (i , j) | j >= V.length b = Just (a V.! i , (i + 1 , j    ))
  go (i , j) = let x = a V.! i ; y = b V.! j in case compare (fst x) (fst y) of
    LT → Just (x , (i + 1 , j    ))
    GT → Just (y , (i     , j + 1))
    EQ → Just ((fst x , f (snd x) (snd y)) , (i + 1 , j + 1))
  in BSM (V.unfoldrN (V.length a + V.length b) go (0 , 0))

--unionWith f a b = let
--  merge f xs [] = xs
--  merge f [] ys = ys
--  merge f (x : xs) (y : ys) = case compare (fst x) (fst y) of
--    LT → x : merge f xs (y : ys)
--    GT → y : merge f (x : xs) ys
--    EQ → (fst x , f (snd x) (snd y)) : merge f xs ys
--  in BitSetMap.fromList (merge f (BitSetMap.toList a) (BitSetMap.toList b))

--intersectionWith ∷ (a → a → c) → BitSetMap a → BitSetMap a → BitSetMap c
intersectionWith f a b = let
  merge _ _ [] = []
  merge _ [] _ = []
  merge f (x : xs) (y : ys) = case compare (fst x) (fst y) of
    LT → merge f xs (y : ys)
    GT → merge f (x : xs) ys
    EQ → (fst x , f (snd x) (snd y)) : merge f xs ys
  in BitSetMap.fromList (merge f (BitSetMap.toList a) (BitSetMap.toList b))

--mergeWithKey ∷ (Key → a → b → Maybe c) → (IntMap a → IntMap c) → (IntMap b → IntMap c) → IntMap a → IntMap b → IntMap c
-- f combines keys when found in both, m1 and m2 says how to deal with both differences
-- eg: merged = BSM.mergeWithKey (\k a b → Just (Both a b)) (fmap LOnly) (BSM.mapWithKey ROnly) x y
--mergeWithKey ∷ (Int → a → b → Maybe c) → (BitSetMap a → BitSetMap c) → (BitSetMap b → BitSetMap c) → BitSetMap a → BitSetMap b → BitSetMap c
--mergeWithKey f onlyL onlyR l r = _
mergeWithKey' ∷ (Int → a → b → Maybe c) → (Int → a → c) → (Int → b → c) → BitSetMap a → BitSetMap b → BitSetMap c
mergeWithKey' both onlyL onlyR l r = let
  ap f (i , v) = (i , f i v)
  merge xs [] = ap onlyL <$> xs
  merge [] ys = ap onlyR <$> ys
  merge (x : xs) (y : ys) = case compare (fst x) (fst y) of
    LT → ap onlyL x : merge xs (y : ys)
    GT → ap onlyR y : merge (x : xs) ys
    EQ → let i = fst x in case both i (snd x) (snd y) of
      Nothing → merge xs ys
      Just v  → (i , v) : merge xs ys
  in BitSetMap.fromList $ merge (BitSetMap.toList l) (BitSetMap.toList r)
mergeWithKey = _

foldrWithKey f z = BSM . foldr (curry f) z . unBSM
singleton i a = BSM (V.singleton (i , a))

{-
-- Patch missing uniqBy
uniqBy f = S.unstream . S.inplace (suniqBy f) S.toMax . S.stream

--uniq ∷ (Eq a, Monad m) ⇒ Stream m a → Stream m a
{-# INLINE_FUSED suniqBy #-}
suniqBy f (S.Stream step st) = let
    {-# INLINE_INNER step' #-}
    step' (Nothing, s) = step s <&> \case
      S.Yield x s' → (S.Yield x (Just x , s'))
      S.Skip  s'   → (S.Skip    (Nothing, s'))
      S.Done       → S.Done
    step' (Just x0, s) = step s <&> \case
      S.Yield x s' → if f x x0 then S.Skip (Just x0, s') else S.Yield x (Just x , s')
      S.Skip  s'   → S.Skip (Just x0, s')
      S.Done       → S.Done
  in S.Stream step' (Nothing,st)
-}
