-- CoreUtils:
--  * lookup INames
--  * prettyprint

module CoreUtils where

import CoreSyn
import qualified Data.Vector as V
import qualified Data.Text as T (unpack)

lookupBinding :: IName -> BindMap -> Binding
 = \n binds -> binds V.! n

typeOfBind :: IName -> BindMap -> Type
 = \n binds -> typed $ info $ lookupBinding n binds

lookupType :: IName -> TypeMap -> Entity
 = flip (V.!)

hNm2Str = T.unpack
