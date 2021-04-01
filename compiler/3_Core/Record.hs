module Record where
import Data.Vector

-- ?? mixfixes , Proj (of dependent / mutual fields)
-- sorted by ifields
-- externs: make sigma type with inferred dependents
-- opened record list

-- ? bis , domain , qtt , local type vars , record qtt
-- ? record mutual dependencies
-- ? opened record

type IField = Int
type FieldName = Int
type Len = Int
data Record tt
  = Field  IField tt                   -- global record space
  | Struct Len [Record tt]             -- independent components
  | Sigma  Len (Record tt) (Record tt) -- second depends on first
  | Mutual Len (Record tt)             -- insane

--------------
-- Solution --
--------------
--lookupNm :: HName -> [FName]
type World = Vector FieldEntry
data FieldEntry = FieldEntry {
   parent     :: FieldName -- parent module usually
 , hName      :: Text
 , dependents :: [FieldName]
}

-- 0. label,TT,dependents,unresolved (backrefs)
-- 1. filter isolates
-- 2. filter mutuals

-- ? lambda functions
-- ? sub records

-- !!
-- lookup
-- shared fnames
-- set of fields
-- dependents
-- save to file
-- incrementally compute types
-- unique the module
--
-- externs // sigma type
