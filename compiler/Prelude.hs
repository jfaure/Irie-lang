{-# LANGUAGE NoImplicitPrelude #-}
module Prelude
 ( module Protolude , module Data.Align , module Data.These , module Control.Arrow
 , Text.Printf.printf , String , Prelude.error , assert , iMap2Vector , fromJust , IName , HName , ModuleIName , argSort , imap , emptyBitSet , setNBits , popCnt , bitSet2IntList , intList2BitSet , bitDiff , BitSet , d_ , dv_ , did_ , anyM , allM , findM , foldl1 , fromRevListN , anaM , hyloM , hypoM , hypoM' , hypo , vecArgSort , unfoldrExactN' , amend , amendU , intLog2 , generateM_)

--  QName(..) , mkQName , unQName , modName , qName2Key , moduleBits)
where
import Protolude hiding (check , Type , Fixity(..) , moduleName , option
 , try , some , many -- conflict with megaparsec
 )

import GHC.Err
import GHC.Stack (HasCallStack , withFrozenCallStack)
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as MVU
import qualified Data.Map.Strict as M
import Data.Align
import Data.These
import Text.Printf
import Control.Arrow ((|||) , (&&&) , (***) , (>>>) , (<<<))
import Control.Exception (assert)
import Data.Functor.Foldable

import qualified Data.Vector.Algorithms.Intro as VAlgo

generateM_ :: Applicative m => Int -> (Int -> m a) -> m ()
generateM_ n f = let go i = if i < n then f i *> go (i + 1) else pure () in go 0

intLog2 x = finiteBitSize x - 1 - countLeadingZeros x

amendU :: VU.Unbox a => VU.Vector a -> Int -> a -> VU.Vector a
amendU v i a = VU.modify (\mv -> MVU.write mv i a) v

amend :: V.Vector a -> Int -> a -> V.Vector a
amend v i a = V.modify (\mv -> MV.write mv i a) v

vecArgSort :: (Ord a, VU.Unbox a) => VU.Vector a -> VU.Vector Int
vecArgSort xs = VU.map fst $ VU.create do
  xsi <- VU.thaw $ VU.indexed xs
  xsi <$ VAlgo.sortBy (comparing snd) xsi

-- return seed also
unfoldrExactN' :: Int -> (b -> (a , b)) -> b -> (V.Vector a , b)
unfoldrExactN' n fU seed = runST do
  v <- MV.new n
  endSeed <- foldM (\s i -> fU s & \(val , seed2) -> seed2 <$ MV.write v i val) seed [0 .. n-1]
  (, endSeed) <$> V.unsafeFreeze v

type BitSet = Integer
type String = [Char]
type IName  = Int
type ModuleIName = Int
type HName  = Text

fromRevListN n l = V.create do
  v <- MV.new n
  v <$ zipWithM (\i e -> MV.write v i e) [n-1,n-2..0] l

--error (s :: String) = panic $ toS s
error :: HasCallStack => String -> s
error s = withFrozenCallStack (trace s (GHC.Err.error s))
fromJust = fromMaybe (panic "fromJust")

popCnt b = let i64List = unfoldr (\b -> if b /= 0 then Just (fromInteger b :: Int64 , b `shift` 64) else Nothing) b in sum $ popCount <$> i64List

foldl1 f (x :| xs) = foldl' f x xs

emptyBitSet = 0 :: Integer
setNBits n = (1 `shiftL` n) - 1 -- setNBits 2 = 0b11
a `bitDiff` b = a .&. complement b

bitSet2IntList :: Integer -> [Int]
bitSet2IntList b = let
  littleEndian = testBit (1::Int) 0
  shift = if littleEndian then shiftR else shiftL
  count = if littleEndian then countTrailingZeros else countLeadingZeros
  i64List = unfoldr (\b -> if b /= 0 then Just (fromInteger b :: Int64 , b `shift` 64) else Nothing) b
  idxs    = unfoldr (\b -> let c = count b in if c == 64 then Nothing else Just (c , clearBit b c)) <$> i64List
  in concat (zipWith (\off i -> map (+off) i) [0,64..] idxs)

intList2BitSet :: Foldable t => t Int -> Integer
intList2BitSet = foldl setBit 0

argSort :: M.Map HName IName -> VU.Vector IName
argSort hmap = let v = VU.fromList (M.elems hmap) in VU.unsafeBackpermute v v

imap f l = zipWith f ([0..] :: [Int]) l

iMap2Vector mp = V.create $ MV.unsafeNew (M.size mp)
  >>= \v -> v <$ (\nm idx -> MV.write v idx nm) `M.traverseWithKey` mp

d_ x   = let --if not global_debug then identity else let
  clYellow  x = "\x1b[33m" ++ x ++ "\x1b[0m"
  in trace (clYellow (show x))
did_ x = d_ x x
dv_ f = traceShowM =<< V.freeze f

findM :: (Foldable f, Monad m) => (a -> m Bool) -> f a -> m (Maybe a)
findM p = foldr (\x f -> p x >>= \case { True -> pure (Just x) ; False -> f }) (pure Nothing)

anyM :: Monad m => (a -> m Bool) -> [a] -> m Bool
anyM f = \case
  []   -> pure False
  x:xs -> do f x >>= \b -> if b then pure True else anyM f xs

allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
allM f = \case
  []   -> pure True
  b:bs -> f b >>= \bv -> if bv then allM f bs else pure False

-- cata f . apo g
hypo   :: (Functor f , Base ff ~ f, Recursive ff) => (f expr -> expr) -> (seed -> f (Either ff seed)) -> seed -> expr
hypo f g = h where h = f <<< fmap (cata f ||| h) <<< g

anaM :: (Corecursive t, Traversable (Base t), Monad m) => (a -> m (Base t a)) -> a -> m t
anaM psi = a where a = fmap embed . traverse a <=< psi

-- There are 2 possible semantics for hypoM: does Left break the hylo or just the apo
hypoM' :: (Traversable t, Monad m) => (t b -> b) -> (c -> m (t (Either b c))) -> c -> m b
hypoM' f g = h where h = fmap f <<< traverse (pure ||| h) <=< g
hypoM :: (Traversable t, Monad m , Base b ~ t, Recursive b)
  => (t b -> b) -> (c -> m (t (Either b c))) -> c -> m b
hypoM f g = h where h = fmap f <<< traverse (pure . cata f ||| h) <=< g

hyloM :: (Functor f , Monad m , Traversable f) => (f b -> b) -> (a -> m (f a)) -> a -> m b
hyloM f g = h where h = fmap f <<< traverse h <=< g


{-# INLINE imap #-}
{-# INLINE anyM #-}
{-# INLINE allM #-}
{-# INLINE intList2BitSet #-}
{-# INLINE bitSet2IntList #-}
{-# INLINE popCnt #-}
{-# INLINE foldl1 #-}
{-# INLINE emptyBitSet #-}
{-# INLINE setNBits #-}
{-# INLINE fromJust #-}
