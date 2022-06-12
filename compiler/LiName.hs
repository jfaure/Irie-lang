module LiName where -- Linear Names; IName + LiName number (dups)

newtype LiName = LiName Int deriving (Show , Eq , Ord)

type LinTable = V.Vector (Int , VName)
