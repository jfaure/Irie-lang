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

unVar :: TypeMap -> Type -> Type = \tyMap x ->
  let checkLoop v seen = case v of
          TyAlias n -> if n `elem` seen
            then error ("alias loop: " ++ show n)
            else checkLoop (typed $ lookupType n tyMap) (n:seen)
          t -> t  -- trivial case
  in  checkLoop x []
