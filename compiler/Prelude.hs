{-# LANGUAGE NoImplicitPrelude #-}
module Prelude ( module Protolude , String , error , panic , iMap2Vector , fromJust) --, module GHC.Show , module GHC.Err , id , String)
where
import Protolude hiding (check , Type , Fixity(..) , moduleName , option
 , try , some , many -- conflict with megaparsec
-- , panic
 )

import GHC.Err
--import Data.Maybe (fromJust) -- admittedly cancerous
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.Map as M

type String = [Char]

--error (s :: String) = panic $ toS s
--
fromJust = fromMaybe (panic "fromJust")

iMap2Vector mp = V.create $ do
  v <- MV.unsafeNew (M.size mp)
  v <$ (\nm idx -> MV.write v idx nm) `M.traverseWithKey` mp
