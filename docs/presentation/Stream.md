# Fold-build
* limitations:
  zip
  foldl
  tail (drop n) , foldr1 don't treat all their Conses equally

# Stream

augment g xs = g (:) xs
build   g    = augment g []

destroy g xs = g (\case { [] -> Nothing ; x:xs => Just (x,xs)} ) xs
unfoldr f b  = case f b of { Nothing->[] ; Just (a,b') -> a : unfoldr f b' }

stream (unstream s) => s
stream :: [a] → Stream a
stream xs0 = Stream (\case { []->Done ; x:xs -> Yield x xs}) xs0

unstream :: Stream a -> [a]
unstream (Stream next0 s0) = let
  unfold s = case next0 s of
    Done       → []
    Skip s0    → unfold s0
    Yield x s0 → x : unfold s0
  in unfold s0

foldr :: (a → b → b) → b → Stream a → b
foldr f z (Stream next s0) = let
  go s = case next s of
    Done       → z
    Skip s0    → go s0
    Yield x s0 → f x (go s0)
  in go s0

map g l = foldr (\y ys -> (g y):ys) [] l

map g (Stream next ss) = let
  go s = case next s of
    Done       -> []
    Skip s0    -> go s0
    Yield x s0 -> g x : go s0
  in go ss

maps :: (a → b) → Stream a → Stream b
maps f (Stream next0 s0) = let
  next s = case next0 s of
    Done       → Done
    Skip s0    → Skip s0
    Yield x s0 → Yield (f x) s0
  in Stream next s0

-- Tests (fold-build)
foldr k y = \case
  []   => z
  x:xs => k x (foldr k z xs)
and = foldr (&&) True
sum = foldr (+) 0
elem x = foldr (\a b => a == x || b) False
filter p = foldr (\a b -> if f a then a:b else b)
append front back = foldr (:) back front
concat = foldr (++) []
foldl f z xs = foldr (\b g a -> g (f a b)) id xs z -- !? suspended function calls isomorphic to the removed list

unlines ls = concat (map (\l -> l ++ ['\n']) ls)
f xs ys = sum (xs ++ ys)
t1 = foldl (+) 0 (concatMap \k => concatMap \m => pure (k * m))
t2 = sum (concatMap (\m => pure (m * m)) (enumFromTo 1 n))
