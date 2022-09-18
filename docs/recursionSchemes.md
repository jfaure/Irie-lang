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
insertLeftmost new = para $ \case -- para pairs the original tree with results of recursion
  -- TreeF Int (Tree Int, Tree Int) -> Tree Int
  NodeF i [] → Node i [Node new []] -- insert new node on left
  NodeF i ((_orig, recur) : tts)) → -- use orignal tree except for leftmost node
    let (origs, _recurs) = unzip tts in Node i (recur : origs)
      -- tts :: [(Tree Int, Tree Int)]
