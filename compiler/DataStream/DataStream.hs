module DataStream.DataStream where
import Data.IntMap.Strict as IM
import CoreSyn

-- 1. eval non-datas
-- 2. eval split-trees
-- 3. eval dataStreams

-- Flat list ; Shared datas

-- f S = G (F S) S
data Generator
 = GenTree Term -- const data tree
 | GenFlat Term -- array | array-like
 | GenRec  Term -- makes Labels recursively

-- stream consumers and temporary streams
data SplitTree
 = End Term
 | Splitter (IM.IntMap SplitTree) -- match
 | Trans [SplitTree] -- composed streams

 | Zipper [SplitTree] -- phi node (merge streams)

data Drain
 = Drain ([IName] , SplitTree) Generator
 | Tap [([IName] , SplitTree)] Generator --share
