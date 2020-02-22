-- Type judgements: checking and inferring
-- To understand this, it is crucial to read "Algebraic subtyping" by Stephen Dolan
-- https://www.cl.cam.ac.uk/~sd601/thesis.pdf

module BiUnify where
import Prim
import CoreSyn as C
import PrettyCore
import qualified CoreUtils as CU

import qualified Data.Vector.Mutable as MV -- mutable vectors
import Control.Monad.ST
import qualified Data.Vector as V
import qualified Data.Map as M
import qualified Data.HashMap.Strict as HM
import qualified Data.IntMap as IM
import qualified Data.Text as T
import Data.Functor
import Control.Monad
import Control.Applicative
import Control.Monad.Trans.State.Strict
import Data.Char (ord)
import Data.List (foldl', intersect)
import GHC.Exts (groupWith)

import Debug.Trace

-- t1 x = x.foo.bar{foo=3}

judgeModule :: CoreModule -> CoreModule
judgeModule cm = let
  startState = TCEnvState
    { binds  = bindings cm
    , biSubs = V.empty
    }
  go = V.imapM judgeBind (V.take (nTopBinds cm) (bindings cm))
  in cm { bindings = binds (execState go startState) }

-- Overloading allows terms (fn calls) to change depending on their type.
data Judged
 = Instance { typeOf :: TyPlus , instanced :: Term }
 | Typed    { typeOf :: TyPlus }
 deriving (Show)

 -- type check environment
type TCEnv a = State TCEnvState a
data TCEnvState = TCEnvState {
   binds  :: BindMap -- monotype env
 , biSubs :: BiSubs  -- typevar  env
}

-- plumbing
updateBind :: IName -> Binding -> BindMap -> BindMap
updateBind n newBind binds = V.modify (\v->MV.write v n newBind) binds
updateBindTy n newTy binds = let
  changeTy x = x{info = (info x){ty = newTy}}
  new = changeTy $ binds V.! n
  in V.modify (\v->MV.write v n new) binds
updateBiSub n f biSubs = let
  newBisub = f $ biSubs V.! n
  in V.modify (\v->MV.write v n newBisub) biSubs
-- monadically update type environments
updateBindM n newBind = modify(\x->x{binds=updateBind n newBind (binds x)})
updateBindTyM n newTy = modify(\x->x{binds=updateBindTy n newTy (binds x)})
updateBiSubM n f = modify(\x->x{biSubs=updateBiSub n f (biSubs x)})
lookupBindM n = gets ((V.! n) . binds)

judgeBind :: IName -> Binding -> TCEnv TyPlus
 = \bindINm -> \case
--    updateInstance bindINm judged = case judged of
--      Typed fnTy      -> updateBindTy bindINm fnTy
--      Instance fnTy e -> updateBind bindINm (\x->x{info=(info x){typed=fnTy} , expr=e})
  LBind inf args e -> do
    inferred <- case args of
      []   ->  infer e
      args -> do -- rule ABS (lambda abstraction); lambda-bound vars start life typed T
        -- register lambda-bounds as T ?
        eTy <- infer e
        argTys <- pure [] --mapM gotTy args TODO
        let t = [THArrow argTys eTy]
        updateBindTyM bindINm (TyJudged t)
        pure t
    tyEnv <- gets id
    pure $ case ty inf of
      TyUser annotation -> if check inferred annotation tyEnv
        then inferred else error $ mkTcFailMsg e annotation inferred
      _ -> inferred
  x -> pure $ (\case{TyJudged t -> t}) $ ty (info x)

infer :: Term -> TCEnv TyPlus
 = \term -> case term of
  -- the type of primitives is non-negotiable
  Lit l  -> pure $ [typeOfLit l]
  Instr p args -> _
  Var nm -> lookupBindM nm >>= judgeBind nm -- lookup type of term-vars in the monotype environment

  -- APP: f : [Df-]ft+ , Pi ^x : [Df-]ft+ ==> e2:[Dx-]tx+
  -- |- f x : biunify [Df n Dx]tx+ under (tf+ <= tx+ -> a)
  -- ie. app introduces typevars
  App fnName args -> _

  Case ofExpr a -> case a of -- biunify the intersection
   -- If has constraints   (t1+ <= bool , t2+<=a , t3+<=a)
   Switch alts -> _ -- sugar for if ?

   -- Proj has constraints (t+ <= {l:a})

-- Biunification handles constraints of the form t+ <= t- by substitution
-- Atomic: (join/meet a type to the var)
-- a  <= t- solved by [m- b = a n [b/a-]t- /a-] 
-- t+ <= a  solved by [m+ b = a u [b/a+]t+ /a+] 
-- a  <= c  solved by [m- b = a n [b/a-]c  /a-] -- (or equivalently,  [a u b /b+])
-- SubConstraints:
-- (t1- -> t1+ <= t2+ -> t2-) = {t2+ <= t1- , t+ <= t2-}
biSub :: TyPlus -> TyMinus -> TCEnv Bool
-- lattice top and bottom
biSub [] _ = pure False
biSub _ [] = pure False
-- atomic constraints
biSub [THVar p] m = updateBiSubM p (\x->x{pSub=m ++ pSub x}) *> pure True -- includes var1 <= var2 case
biSub p [THVar m] = updateBiSubM m (\x->x{mSub=p ++ mSub x}) *> pure True
-- lattice subconstraints
biSub (p1:p2:p3) m = biSub [p1] m *> biSub (p2:p3) m
biSub p (m1:m2:m3) = biSub p [m1] *> biSub p (m2:m3)
-- head constructor subconstraints
biSub [THArrow pArgs pRet] [THArrow mArgs mRet] = zipWithM biSub mArgs pArgs *> biSub pRet mRet
biSub [THRec i p] m = _
biSub p [THRec i m] = _
-- Other; biSub is partial, since subtyping isn't defined between all type components
biSub _ _ = pure False

-- reduced form: unroll mus and merge components, eg.
-- {l1:a} u {l1:b,l2:b} u mg.a->g
-- {l1:aub}ua -> (mg.a->g)
reduceType :: [TyHead] -> [TyHead]
reduceType []  = []
reduceType t = t
--reduceType (t1:tys) = let
--  mergeTy :: [TyHead] -> [TyHead] -> [TyHead]
--  mergeTy ty []     = ty
--  mergeTy ty (tc:tcs) = if eqTyHead tc ty then (ty:tc:tcs) else mergeTy tcs ty
--  mergeTy (THRec i t) tList = t -- TODO unroll
--  in foldr mergeTy t1 tys

-- biunification solves constraints `t+ <= t-` , but checking questions have the form `t- <= t+ ?`
-- we have t1<=t2 and t1<=t3 ==> t1 <= t2ut3
-- reduced form: the join/meets need are all between different components of the type lattice
-- additionally, subsumption <===> equivalence of typing schemes
-- ie. to decide [d1]t1 <= [d2]t2, we check alpha-equivalence of [d1 n d2]t1 u t2 with [d2]t2
check :: [TyHead] -> Type -> TCEnvState -> Bool
check gotRaw (Type uni expRaw) delta = let
  gotTy = reduceType gotRaw ; expTy = reduceType expRaw
  _check ty = True
  in  all _check gotTy

mkTcFailMsg gotTerm gotTy expTy =
  ("subsumption failure:"
  ++ "\nExpected: " ++ show expTy
  ++ "\nGot:      " ++ show gotTy
-- ++ "\n" ++ show (unVar gotTy) ++ " <:? " ++ show expected
  ++ "\nIn the expression: " ++ show gotTy
  )

typeOfLit = \case
  String{} -> THPrim $ PtrTo (PrimInt 8) --"CharPtr"
  Array{}  -> THPrim $ PtrTo (PrimInt 8) --"CharPtr"
--  PolyFrac{} -> realCls
--  _ -> numCls

eqTyHead a b = kindOf a == kindOf b
kindOf THPrim{}  = KPrim
kindOf THAlias{} = _ -- have to deref it
kindOf THVar{}   = KVar
kindOf THArrow{} = KArrow
kindOf THRec{}   = _
kindOf THData{}  = KData
