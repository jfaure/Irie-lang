{-# LANGUAGE DeriveDataTypeable , DeriveFoldable , DeriveTraversable , GeneralizedNewtypeDeriving , InstanceSigs #-}
-- product | sumtype keys are static lists usually consisting of many neighboring bounded integers
-- insertion is O(n), other operations are more space efficient fast
-- fromList O(n)
-- (!?) O(1)
-- union , intersection , mergeWithKey O(n)
module BitSetMap (BitSetMap , size , fromList , fromListWith , BitSetMap.toList , foldrWithKey , singleton , (!?) , BitSetMap.elems 
  , unionWith , intersectionWith , traverseWithKey , mergeWithKey' , mergeWithKey , mapAccum , mapWithKey) where
--import Data.IntMap
--import qualified Data.Vector as V
--type BitSetMap = IntMap
--toList = Data.IntMap.toList
--mergeWithKey' = _
--elems = V.fromList . Data.IntMap.elems

-- dichotomy lookup on a (Vector (Int , a)) is a clear improvement for Data.IntMap for static ordered lists
import qualified Data.Vector as V
import qualified Data.Traversable as DT
import Data.Binary
import GHC.Generics
import Data.Vector.Binary()

newtype BitSetMap a = BSM { unBSM :: V.Vector (Int , a) }
  deriving (Eq , Generic , Show)
instance (Binary e) => Binary (BitSetMap e)
--instance Semialign BitSetMap where
--  alignWith f = mergeWithKey (\k a b -> f (These a b)) (\k x -> f (This x)) (\k y -> f (That y))
instance Functor BitSetMap where
  fmap f = BSM . fmap (\(a , b) -> (a , f b)) . unBSM
instance Foldable BitSetMap where
  foldr :: (a -> b -> b) -> b -> BitSetMap a -> b
  foldr f z = foldr (\(a , b) acc -> f b acc) z . unBSM
instance Traversable BitSetMap where
  traverse f = fmap BSM . traverse (\(a,b) -> (a,) <$> f b) . unBSM

size       = V.length . unBSM
toList   l = V.toList (unBSM l)
fromList l = BSM (V.fromList (sortOn fst l))

fromListWith :: (b -> b -> b) -> [(Int , b)] -> BitSetMap b
fromListWith f l = let
  combine (a : b : l) = if ((==) `on` fst) a b then combine ((fst a , (f `on` snd) a b) : l) else a : combine (b : l)
  combine l = l
  in BSM $ V.fromList (combine (sortOn fst l))

read = \(BSM v) i -> v V.! binarySearch v i 0 (V.length v - 1)
(!?) = \v i -> let r = read v i in if fst r == i then Just (snd r) else Nothing

binarySearch :: V.Vector (Int , a) -> Int -> Int -> Int -> Int
binarySearch = \v e -> let
   -- binary search in [l,u) (start at 0 (length vec))
   loop l u = if u <= l then l else let k = (u + l) `div` 2 in case compare (fst (v V.! k)) e of
     EQ -> k
     LT -> loop (k + 1) u
     GT -> loop l k
  in loop

elems = fmap snd . unBSM

mapAccum :: (a -> b -> (a, c)) -> a -> BitSetMap b -> (a, BitSetMap c)
mapAccum f seed bsm = let
  accFn acc (i , v) = let (next , c) = f acc v in (next , (i , c))
  (r , v) = DT.mapAccumL accFn seed (unBSM bsm)
  in (r , BSM v)

mapWithKey :: (Int -> v -> b) -> BitSetMap v -> BitSetMap b
mapWithKey f = BSM . V.map (\(l , v) -> (l , f l v)) . unBSM

traverseWithKey f = fmap BSM <$> traverse (\(l , v) -> (l ,) <$> f l v) . unBSM

unionWith :: (a -> a -> a) -> BitSetMap a -> BitSetMap a -> BitSetMap a
unionWith f (BSM a) (BSM b) = let
  go (i , j) | i >= V.length a && i >= V.length b = Nothing
  go (i , j) | i >= V.length a = Just (b V.! j , (i     , j + 1))
  go (i , j) | j >= V.length b = Just (a V.! i , (i + 1 , j    ))
  go (i , j) = let x = a V.! i ; y = b V.! j in case compare (fst x) (fst y) of
    LT -> Just (x , (i + 1 , j    ))
    GT -> Just (y , (i     , j + 1))
    EQ -> Just ((fst x , f (snd x) (snd y)) , (i + 1 , j + 1))
  in BSM (V.unfoldrN (V.length a + V.length b) go (0 , 0))

--unionWith f a b = let
--  merge f xs [] = xs
--  merge f [] ys = ys
--  merge f (x : xs) (y : ys) = case compare (fst x) (fst y) of
--    LT -> x : merge f xs (y : ys)
--    GT -> y : merge f (x : xs) ys
--    EQ -> (fst x , f (snd x) (snd y)) : merge f xs ys
--  in BitSetMap.fromList (merge f (BitSetMap.toList a) (BitSetMap.toList b))

intersectionWith :: (a -> a -> c) -> BitSetMap a -> BitSetMap a -> BitSetMap c
intersectionWith f a b = let
  merge f xs [] = []
  merge f [] ys = []
  merge f (x : xs) (y : ys) = case compare (fst x) (fst y) of
    LT -> merge f xs (y : ys)
    GT -> merge f (x : xs) ys
    EQ -> (fst x , f (snd x) (snd y)) : merge f xs ys
  in BitSetMap.fromList (merge f (BitSetMap.toList a) (BitSetMap.toList b))

--mergeWithKey :: (Key -> a -> b -> Maybe c) -> (IntMap a -> IntMap c) -> (IntMap b -> IntMap c) -> IntMap a -> IntMap b -> IntMap c
-- f combines keys when found in both, m1 and m2 says how to deal with both differences
-- eg: merged = BSM.mergeWithKey (\k a b -> Just (Both a b)) (fmap LOnly) (BSM.mapWithKey ROnly) x y
--mergeWithKey :: (Int -> a -> b -> Maybe c) -> (BitSetMap a -> BitSetMap c) -> (BitSetMap b -> BitSetMap c) -> BitSetMap a -> BitSetMap b -> BitSetMap c
--mergeWithKey f onlyL onlyR l r = _
mergeWithKey' :: (Int -> a -> b -> Maybe c) -> (Int -> a -> c) -> (Int -> b -> c) -> BitSetMap a -> BitSetMap b -> BitSetMap c
mergeWithKey' both onlyL onlyR l r = let
  ap f (i , v) = (i , f i v)
  merge xs [] = ap onlyL <$> xs
  merge [] ys = ap onlyR <$> ys
  merge (x : xs) (y : ys) = case compare (fst x) (fst y) of
    LT -> ap onlyL x : merge xs (y : ys)
    GT -> ap onlyR y : merge (x : xs) ys
    EQ -> let i = fst x in case both i (snd x) (snd y) of
      Nothing -> merge xs ys
      Just v  -> (i , v) : merge xs ys
  in BitSetMap.fromList $ merge (BitSetMap.toList l) (BitSetMap.toList r)
mergeWithKey = _

foldrWithKey f z = BSM . foldr (curry f) z . unBSM
singleton i a = BSM (V.singleton (i , a))

{-
-- Patch missing uniqBy
uniqBy f = S.unstream . S.inplace (suniqBy f) S.toMax . S.stream

--uniq :: (Eq a, Monad m) => Stream m a -> Stream m a
{-# INLINE_FUSED suniqBy #-}
suniqBy f (S.Stream step st) = let
    {-# INLINE_INNER step' #-}
    step' (Nothing, s) = step s <&> \case
      S.Yield x s' -> (S.Yield x (Just x , s'))
      S.Skip  s'   -> (S.Skip    (Nothing, s'))
      S.Done       -> S.Done
    step' (Just x0, s) = step s <&> \case
      S.Yield x s' -> if f x x0 then S.Skip (Just x0, s') else S.Yield x (Just x , s')
      S.Skip  s'   -> S.Skip (Just x0, s')
      S.Done       -> S.Done
  in S.Stream step' (Nothing,st)
-}

-- (BitSet , Vector a)
  {-
import Prelude hiding (get , put)
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import Data.Binary
import Data.Vector.Binary()

type Key = Int

data BitSetMap a = BitSetMap {
   indices  :: BitSet
 , contents :: V.Vector a
} deriving (Show , Eq , Generic)

-- Not exported
calculateIdx is key = popCount (is .&. setNBits (key + 1)) - 1
(!) = \(BitSetMap is as) key -> as V.! calculateIdx is key

instance (Binary e) => Binary (BitSetMap e) where
    put (BitSetMap is as) = put is <> put as
    get = get >>= \is -> get <&> \l -> BitSetMap is l
instance Functor BitSetMap where fmap f (BitSetMap is as) = BitSetMap is (f <$> as)
instance Foldable BitSetMap where foldr = BitSetMap.foldr
instance Traversable BitSetMap where traverse f (BitSetMap is as) = BitSetMap is <$> (f `traverse` as)
instance Semialign BitSetMap where
  alignWith f = mergeWithKey (\k a b -> f (These a b)) (\k x -> f (This x)) (\k y -> f (That y))

mapWithKey f (BitSetMap is as) = (BitSetMap is (V.zipWith f (V.fromListN (popCount is) $ bitSet2IntList is) as))

-- sorts in O(n)
fromList l = let
  is = intList2BitSet (fst <$> l)
  es = V.create $ MV.new (popCount is) >>= \v -> v <$ (l `forM` \(i , e) -> MV.write v (calculateIdx is i) e)
  in BitSetMap is es

-- fromList with a combining function for duplicates
fromListWith f l = let
  is = intList2BitSet (fst <$> l)
  es = let
    go v = l `forM` \(i , e) -> do
      gets (`testBit` i) >>= \case
        False -> modify (`setBit` i) *> MV.write v (calculateIdx is i) e
        True  -> MV.modify v (`f` e) i
    in V.create (MV.new (popCount is) >>= \v -> v <$ (go v `evalStateT` emptyBitSet))
  in BitSetMap is es

toList (BitSetMap is contents) = zip (bitSet2IntList is) (V.toList contents)

singleton k a = BitSetMap (0 `setBit` k) (V.singleton a)

(!?) = \(BitSetMap is contents) key -> if is `testBit` key
  then Just (contents V.! popCount (is .&. setNBits key))
  else Nothing

elems = V.toList . contents

foldr = _
foldrWithKey :: (Key -> a -> b -> b) -> b -> IntMap a -> b
foldrWithKey = _
mapAccum = _
traverseWithKey = _

unionWith f a@(BitSetMap ia ea) b@(BitSetMap ib eb) = let
  common = ia .|. ib
  go i = case (ia `testBit` i , ib `testBit` i) of
    (True , True)  -> f (a ! i) (b ! i)
    (True , False) -> a ! i
    (False , True) -> b ! i
  in BitSetMap common $ V.fromListN (popCount common) (go <$> bitSet2IntList common)

intersectionWith f a@(BitSetMap ia ea) b@(BitSetMap ib eb) = let common = ia .&. ib
  in BitSetMap common $ V.fromListN (popCount common) ((\i -> f (a ! i) (b ! i)) <$> bitSet2IntList common)

--mergeWithKey :: (Key -> a -> b -> Maybe c) -> (IntMap a -> IntMap c) -> (IntMap b -> IntMap c) -> IntMap a -> IntMap b -> IntMap c
-- f combines keys when found in both, m1 and m2 says how to deal with both differences
{-# INLINE mergeWithKey #-}
mergeWithKey :: (Key -> a -> b -> c) -> (Key -> a -> c) -> (Key -> b -> c)
  -> BitSetMap a -> BitSetMap b -> BitSetMap c
mergeWithKey combine only1 only2 a@(BitSetMap ia ea) b@(BitSetMap ib eb) = let
  common = ia .&. ib
  (iOnly1 , iOnly2) = let compCommon = complement common in (ia .&. compCommon , ib .&. compCommon)
  iFinal = iOnly1 .|. iOnly2 .|. common
  eFinal = V.create $ MV.new (popCount iFinal) >>= \v -> v <$ do
    bitSet2IntList iOnly1 `forM` \i -> MV.write v (calculateIdx iFinal i) (only1 i (a ! i))
    bitSet2IntList iOnly2 `forM` \i -> MV.write v (calculateIdx iFinal i) (only2 i (b ! i))
    bitSet2IntList common `forM` \i -> MV.write v (calculateIdx iFinal i) (combine i (a ! i) (b ! i))
  in BitSetMap iFinal eFinal

-- Tests
-- m1 = fromList [(1 , "a") , (9 , "c") , (10 , "f") , (8 , "x")]
-- m2 = fromList [(5 , "5") , (8 , "2") , (1 , "1")]
-- 
-- m3 = intersectionWith (++) m1 m2
-- m4 = unionWith (++) m1 m2
-- 
-- data Test a = LOnly a | ROnly Key a | Both a a deriving Show
-- test = mergeWithKey (\k a b -> Both a b) (const LOnly) (ROnly) m1 m2
-}
