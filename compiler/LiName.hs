module LiName where -- Linear Names; IName + LiName number (dups)
import CoreSyn
import qualified Data.Vector as V

newtype LiName = LiName Int deriving (Show , Eq , Ord)

type LinTable = V.Vector (Int , VName)
