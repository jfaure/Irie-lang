{-# language LambdaCase, MultiWayIf, ScopedTypeVariables, PartialTypeSignatures #-}
module Match where

import qualified Data.Vector as V
import Data.List.Split
import Data.List

type Shape = [Int]
data Tensor = Tensor {
  shape :: Shape
, ravel :: [Int]
}

idot shape = 
 let n = foldr (*) 1 shape
 in  Tensor shape [0..n-1]

instance Show Tensor where
  show (Tensor shape ravel) =
    let go :: Int -> Int -> Shape -> [Int] -> String
        go off r [] [i] = error "" -- show i
        go off r [s] ravel = concat$intersperse " " $ show <$> ravel
        go off r (s:rem) ravel =
          let nLines = take off (repeat '\n')
              chunkLen = r `quot` s
              subLists = chunksOf chunkLen ravel
          in concat $ intersperse nLines $
             (go (off-1) chunkLen rem)<$>subLists
    in go (length shape - 1) (length ravel) shape ravel

-- rank0
match :: (Int->Int) -> (Tensor -> Tensor)
match f = \(Tensor shape ravel) -> f <$> ravel

match2 :: (Int->Int->Int) -> (Tensor->Tensor->Tensor)
match2 f = go where
  go = \(Tensor s1 s2) (\Tensor r1 r2) -> case (s1,s2) of
    ([] , rem)          -> matchRem
    (s1:rem1 , s2:rem2) -> if s1 /= s2 then error "length error" else
      let chunkLen1 = rLen1 `quot` s1
          chunkLen2 = rLen2 `quot` s2
      in  match (f <$>) y $ ar

go = match (-) (idot [2,3])
