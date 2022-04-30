-- IntMap for keys consisting of many neighboring bounded integers
-- insertion is O(n), other operations are very space efficient and very fast
-- fromList O(n)
-- (!?) O(1)
-- union , intersection , mergeWithKey O(n)
module BitSetMap (BitSetMap , fromList , fromListWith , BitSetMap.toList , foldrWithKey , singleton , (!?) , elems 
  , unionWith , intersectionWith , mergeWithKey , traverseWithKey , mapAccum , mapWithKey) where
import Data.IntMap
type BitSetMap = IntMap
toList = Data.IntMap.toList
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
