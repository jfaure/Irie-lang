-- CoreUtils: 
--  * lookup INames
--  * prettyprint

module CoreUtils where

import CoreSyn
import qualified Data.Vector as V

lookupBinding :: IName -> CoreModule -> Binding
 = \n cm -> (bindings cm) V.! n     

lookupType :: IName -> CoreModule -> Type
 = \n cm -> 
 let bind = lookupBinding n cm
 in typed $ info bind
