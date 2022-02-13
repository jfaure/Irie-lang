{-# LANGUAGE NoImplicitPrelude #-}
module Prelude ( module Protolude , module Data.Align , module Data.These , Text.Printf.printf , String , error , iMap2Vector , fromJust , IName , HName , ModuleIName , argSort , imap , emptyBitSet , setNBits , bitSet2IntList , intList2BitSet , bitDiff , BitSet , d_ , dv_ , did_)

--  QName(..) , mkQName , unQName , modName , qName2Key , moduleBits)
where
import Protolude hiding (check , Type , Fixity(..) , moduleName , option
 , try , some , many -- conflict with megaparsec
 )

import GHC.Err
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector.Unboxed as VU
import qualified Data.Map.Strict as M
import Data.Align
import Data.These
import Text.Printf

type Nat    = Int
type BitSet = Integer
type String = [Char]
type IName  = Int
type ModuleIName = Int
type HName  = Text

--error (s :: String) = panic $ toS s
fromJust = fromMaybe (panic "fromJust")

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

intList2BitSet :: [Int] -> Integer
intList2BitSet = foldl setBit 0

argSort :: Int -> M.Map HName IName -> VU.Vector IName
argSort n hmap = let v = VU.fromList (M.elems hmap) in VU.unsafeBackpermute v v

imap f l = zipWith f ([0..] :: [Int]) l

iMap2Vector mp = V.create $ do
  v <- MV.unsafeNew (M.size mp)
  v <$ (\nm idx -> MV.write v idx nm) `M.traverseWithKey` mp

d_ x   = let --if not global_debug then identity else let
  clYellow  x = "\x1b[33m" ++ x ++ "\x1b[0m"
  in trace (clYellow (show x))
did_ x = d_ x x
dv_ f = traceShowM =<< V.freeze f


