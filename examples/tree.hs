-- The prefix is a little tricky to handle
-- when a dir is opened, append "|-- " to prefix,
-- and remove the previous "--"
-- the last entry in a dir is   "`-- "
-- when a dir is closed, remove the "|-- "
tree : String -> IO ()
tree rootPath = puts rootPath *> subTree "|-- " rootPath where
  subTree : (prefix : String | prefix.count>=4) -> String -> IO ()
   = \prefix path -> do
    (entries;last) <- Dir::entries path >>= filter (\e->e.0 != '.') . splitAt -1
    let inDirPrefix = dropTail 3 prefix , "   " -- "|   "
        endDirPrefix = dropTail 4 prefix , "`-- " -- prefix . set -4 '`'
        handleEntry prefix entry = puts (prefix , File::basename entry)
                                   *> subTree (prefix , "|-- ") entry
    entries . each (handleEntry inDirPrefix)
    *> handleEntry endDirPrefix last

main : Int -> [String] -> IO ()
main ac [] = tree =<< Dir::pwd
main ac av = mapM_ tree av

-- Requires:
-- File::basename : String->String
-- Dir::entries   : IO [String]
