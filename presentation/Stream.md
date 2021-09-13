# Fold-build
* limitations:
  zip
  foldl
  tail (drop n) , foldr1 don't treat all their Conses equally

# Stream

augment g xs = g (:) xs
build   g    = augment g []

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
