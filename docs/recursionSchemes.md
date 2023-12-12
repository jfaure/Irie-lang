-- pretty print a tree
let pprint1 :: Tree Int -> String
    pprint1 = fold \case
      NodeF i [] -> show i
      NodeF i ss -> show i ++ ": [" ++ intercalate ", " ss ++ "]"

let pprint2 :: Tree Int -> String
    pprint2 = flip runReader 0 . cataA go
      where
        go :: TreeF Int (Reader Int String) -> Reader Int String
        go (NodeF i rss) = do
          -- rss :: [Reader Int String]
          -- ss  :: [String]
          ss <- local (+ 2) $ sequence rss
          indent <- ask
          let s = replicate indent ' ' ++ "* " ++ show i
          pure $ intercalate "\n" (s : ss)

let pprint3 :: Tree Int -> String
    pprint3 t = cataA go t 0
      where
        go :: TreeF Int (Int -> String) -> Int -> String
        go (NodeF i fs) indent
            -- fs :: [Int -> String]
          = let indent' = indent + 2
                ss = map (\f -> f indent') fs
                s = replicate indent ' ' ++ "* " ++ show i
            in intercalate "\n" (s : ss)

-- Add number to each node indicating count of children below it
let pprint4 :: Tree Int -> String
    pprint4 = flip runReader 0 . para go
      where
        go :: TreeF Int (Tree Int, Reader Int String) -> Reader Int String
        go (NodeF i trss) = do
          -- trss :: [(Tree Int, Reader Int String)]
          -- ts   :: [Tree Int]
          -- rss  :: [Reader Int String]
          -- ss   :: [String]
          let (ts, rss) = unzip trss
          let count = sum $ fmap length ts
          ss <- local (+ 2) $ sequence rss
          indent <- ask
          let s = replicate indent ' '
               ++ "* " ++ show i
               ++ " (" ++ show count ++ ")"
          pure $ intercalate "\n" (s : ss)

-- re-use most subtrees from the original
let insertLeftmost :: Int -> Tree Int -> Tree Int
    insertLeftmost new = para go
      where
        go :: TreeF Int (Tree Int, Tree Int)
           -> Tree Int
        go (NodeF i []) = Node i [Node new []]
        go (NodeF i ((_orig, recur) : tts))
            -- tts :: [(Tree Int, Tree Int)]
          = let (origs, _recurs) = unzip tts
            in Node i (recur : origs)

fib :: Natural -> Integer
fib = histo go
  where
    go :: Maybe (Cofree Maybe Integer) -> Integer
    go Nothing = 1
    go (Just (_ :< Nothing)) = 1
    go (Just (fibNMinus1 :< Just (fibNMinus2 :< _)))
      = fibNMinus1 + fibNMinus2

-- github compression algorithm
rollup :: [Cofree (TreeF node) label] -> ([node], [label])
rollup [_ :< NodeF node cofrees] = let
  (nodes, label) = rollup cofrees
   in (node : nodes, label)
rollup cofrees = ([], fmap extract cofrees)

foobar xs = 1 :< NodeF "foo" [2 :< NodeF "bar" xs]

rollup [foobar []] --  (["foo","bar"],[])
rollup [foobar [3 :< NodeF "baz" [], 4 :< NodeF "quux" []]] -- (["foo","bar"],[3,4])

--The value foobar [] can be interpreted as the tree NodeF "foo" [NodeF "bar" []], plus two annotations.
--The "foo" node is annotated with 1, while the "bar" node is annotated with 2.
--When we call histo below, those annotations are recursive results of type Int -> String.
pprint5 :: Tree Int -> String
pprint5 t = let
  go :: TreeF Int (Cofree (TreeF Int) (Int -> String)) -> Int -> String
  go (NodeF node cofrees) indent
      -- cofrees :: [Cofree (TreeF Int) (Int -> String)]
      -- fs :: [Int -> String]
    = let indent' = indent + 2
          (nodes, fs) = rollup cofrees
          ss = map (\f -> f indent') fs
          s  = replicate indent ' ' ++ "* " ++ intercalate " / " (fmap show (node : nodes))
      in intercalate "\n" (s : ss)
  in histo go t 0

--One common use for para is to construct a new tree which reuses most of the sub-trees from the original. In the following example, we insert a new node under the leftmost leaf. This requires allocating new nodes along a path from the root to that leaf, while keeping every other sub-tree untouched.

insertLeftmost :: Int -> Tree Int -> Tree Int
insertLeftmost new = para \case -- para pairs the original tree with results of recursion
  -- TreeF Int (Tree Int, Tree Int) -> Tree Int
  NodeF i [] → Node i [Node new []] -- insert new node on left
  NodeF i ((_orig, recur) : tts)) → -- use orignal tree except for leftmost node
    let (origs, _recurs) = unzip tts in Node i (recur : origs)
      -- tts :: [(Tree Int, Tree Int)]

collatzLength :: Int -> Int
collatzLength = let
  algebra Nil        = 0
  algebra (Cons _ x) = x + 1
  elgotCoalgebra 1 = Left 1
  elgotCoalgebra n = Right $ Cons n if n `mod` 2 == 0 then (div n 2) else (3 * n + 1)
  in elgot algebra elgotCoalgebra

cata  :: (Base t (Identity a) -> a) -> t -> a
para  :: (Base t (t, a) -> a) -> t -> a
histo :: (Base t (Cofree (Base t) a) -> a) -> t -> a
-- All are comonads

-- mendler

mcata doesn't need Functor (Base t) constraint, but instead in your mendlerAlg you'll need to kind-of do parts of fmap.

mcata :: (forall y. (y -> c) -> f y -> c) -> Fix f -> c
the forall y. (y -> c) -> f y part is isomorphic to f c (Yoneda), where the evidence in forward direction is fmap.

EDIT: why it's neat. Because in some cases you can coerce, which is potentially a lot cheaper than fmap! In other words, as a user you have to do more (do fmapping), but you also have opportunity to that more efficiently.

-- >>> putStr $ decompressImage [(1,'.'),(1,'*'),(3,'.'),(4,'*')]
-- .*.
-- ..*
-- ***
decompressImage :: [(Int,Char)] -> String
decompressImage = chrono linesOf3 decodeRLE where
  decodeRLE :: [(Int,Char)] -> ListF Char (Free (ListF Char) [(Int,Char)])
  decodeRLE []          = Nil
  decodeRLE ((n,c):ncs) = Cons c do
    replicateM_ (n-1) $ Free $ Cons c $ Pure ()
    pure ncs

  linesOf3 :: ListF Char (Cofree (ListF Char) String) -> String
  linesOf3 (Cons c1 (_ :< Cons c2 (_ :< Cons c3 (cs :< _)))) = c1:c2:c3:'\n':cs
  linesOf3 _
