{-# LANGUAGE NoImplicitPrelude #-}
module Prelude ( module Protolude , String , error , iMap2Vector , fromJust , IName , HName , ModuleIName , argSort , imap)
where
import Protolude hiding (check , Type , Fixity(..) , moduleName , option
 , try , some , many -- conflict with megaparsec
 )

import GHC.Err
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector.Unboxed as VU
import qualified Data.Map as M

type String = [Char]
type IName  = Int
type ModuleIName = Int
type HName  = Text

--error (s :: String) = panic $ toS s
fromJust = fromMaybe (panic "fromJust")

argSort :: Int -> M.Map HName IName -> VU.Vector IName
argSort n hmap = let v = VU.fromList (M.elems hmap) in VU.unsafeBackpermute v v

imap f l = zipWith f ([0..] :: [Int]) l

iMap2Vector mp = V.create $ do
  v <- MV.unsafeNew (M.size mp)
  v <$ (\nm idx -> MV.write v idx nm) `M.traverseWithKey` mp
