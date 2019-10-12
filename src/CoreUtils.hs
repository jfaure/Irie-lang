-- CoreUtils:
--  * lookup INames
--  * prettyprint

module CoreUtils where

import CoreSyn
import qualified Data.Vector as V

lookupBinding :: IName -> ExprMap -> Binding
 = \n binds -> binds V.! n

lookupType :: IName -> ExprMap -> Type
 = \n binds -> typed $ info $ lookupBinding n binds
