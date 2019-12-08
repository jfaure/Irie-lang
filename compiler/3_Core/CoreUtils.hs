module CoreUtils where

import CoreSyn
import Prim
import qualified Data.Vector as V
import qualified Data.Text as T (unpack)
import Control.Monad.State.Strict

import Debug.Trace

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

localState :: State s a -> State s a
localState f = get >>= \s -> f <* put s

getArity :: Type -> Int = \case
  TyArrow t   -> length t - 1
  TyPAp t1 t2 -> length t2 - 1
  TyMono (MonoTyPrim p) -> case p of
    PrimExternVA l -> length l -- at least
    PrimExtern   l -> length l - 1
  TyExpr (TyTrivialFn _ t) -> getArity t
  o -> trace ("warning: getArity on non-function: " ++ show o) 0
