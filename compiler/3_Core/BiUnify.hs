-- Type judgements: checking and inferring
-- To understand this, it is crucial to read "Algebraic subtyping" by Stephen Dolan
-- https://www.cl.cam.ac.uk/~sd601/thesis.pdf

module BiUnify where
import Prim
import qualified ParseSyntax as P
import CoreSyn as C
import TCState
import PrettyCore
import qualified CoreUtils as CU
import DesugarParse

import qualified Data.Vector.Mutable as MV -- mutable vectors
import Control.Monad.ST
import qualified Data.Vector as V
import qualified Data.Map as M
import qualified Data.IntMap as IM
import qualified Data.Text as T
import Data.Functor
import Control.Monad
import Control.Applicative
import Control.Monad.Trans.State.Strict
import Data.Char (ord)
import Data.List --(foldl', intersect)
import GHC.Exts (groupWith)
import Control.Lens
--import Data.Vector.Lens

import Debug.Trace
d_ x   = trace (clYellow (show x))
did_ x = d_ x x

-- test1 x = x.foo.bar{foo=3}

-- output is a list of CBind's with type/kind annotation
-- type check environment

judgeModule :: P.Module -> V.Vector Bind
judgeModule pm = let
  nBinds = length $ pm ^. P.bindings
  start = TCEnvState
    { _pmodule = pm
    , _biSubs  = V.empty
    , _wip     = V.replicate nBinds WIP
    }
  go  = mapM_ judgeBind [0 .. nBinds-1]
  end = execState go start
  in end ^. wip

judgeBind :: IName -> TCEnv Bind
 = \bindINm -> (V.! bindINm) <$> use wip >>= \t -> case t of
  E argNms eta     -> pure t
  B arNms term ty  -> pure t
  T tArgs ty       -> pure t
  WIP -> do
    P.FunBind hNm matches tyAnn <- (!! bindINm) <$> use (id . pmodule . P.bindings)
    let (args , tt) = matches2TT matches
        nArgs = length args
    biSubs .= (V.generate nArgs (\i -> BiSub [THVar i] [THVar i]))
    res <- infer tt
    (argSubs , bis) <- (\v -> V.splitAt (V.length v - nArgs) v) <$> use biSubs
    biSubs .= bis
    let argTys = _mSub <$> argSubs
    case tyAnn of
      _ -> pure res
--    Nothing -> pure res
--    Just t  -> check res tyAnn <$> use wip >>= \case
--      True  -> pure res
--      False -> error $ "no unify" -- mkTCFailMsg e tyAnn res
    let newBind = case res of
          Core x t -> B args x [THArrow (V.toList argTys) t]
          Ty   t   -> T [] t -- args ?
    wip %= V.modify (\v->MV.write v bindINm newBind)
    pure newBind

infer :: P.TT -> TCEnv Expr
 = let
 dropArgTy = \case
   Core x ty -> x
   Ty t      -> error "can't drop type"
 getArgTy  = \case
   Core x ty -> ty
   Ty t      -> [THHigher 1] -- type of types
 in \case
  -- vars : lookup in the environment
  P.Var v -> case v of
    P.VBind b   ->    -- polytype env
      judgeBind b <&> \case { B args e ty  -> Core (Var b) ty }
    P.VLocal l  -> do -- monotype env
      ty <- _pSub . (V.! l) <$> use biSubs
      pure $ Core (Arg l) ty
    P.VExtern i -> (!! i) <$> use (pmodule . P.imports) >>= \case
      P.NoScope nm -> pure $ case nm of
        "+"   -> Core (PrimOp (IntInstr Add)) [THArrow [[THPrim (PrimInt 32)]] [THPrim (PrimInt 32)]]
        "Int" -> Ty   [THPrim (PrimInt 32)]
    x -> error $ show x
    _ -> _
  P.WildCard -> _

  ---------------------
  -- lambda calculus --
  ---------------------
  P.Abs fnmatch -> _

  -- APP: f : [Df-]ft+ , Pi ^x : [Df-]ft+ ==> e2:[Dx-]tx+
  -- |- f x : biunify [Df n Dx]tx+ under (tf+ <= tx+ -> a)
  -- * introduce a typevar 'a', and biunify (tf+ <= tx+ -> a)
  P.App f args -> do
    f'   <- infer f
    args'<- mapM infer args
    retTy <- do
      idx <- V.length <$> use biSubs
      biSubs %= (`V.snoc` newBiSub) -- add a fresh typevar for the return type
      biSub_ (getArgTy f') [THArrow (getArgTy <$> args') [THVar idx]] -- can fail
      _pSub . (V.! idx) . did_ <$> use biSubs
    pure $ case foldl' ttApp f' args' of
      Core f _ -> Core f retTy
      t -> t
--  pure $ case f' of
--    (Core f'' ty) -> Core (App f'' (dropArgTy <$> args')) retTy
--    x -> error $ "not ready for " ++ show x

  P.InfixTrain lArg train -> infer $ resolveInfixes _ lArg train

  -------------------
  -- tt primitives --
  -------------------
  -- If has constraints   (t1+ <= bool , t2+<=a , t3+<=a) (biunify the intersection)
  -- Proj has constraints (t+ <= {l:a})
  -- proj, label, cons, match, list

  ---------------------
  -- term primitives --
  ---------------------
  P.Lit l  -> pure $ Core (Lit l) [typeOfLit l] -- the type of primitives is non-negotiable
  P.PrimOp p -> _

  ---------------------
  -- type primitives --
  ---------------------
  P.TyLit primTy -> pure $ Ty [THPrim primTy]

  -- arrows may contain types or eta-expansions
  P.TyArrow tys  -> do -- type given to an Abs
    arrows <- mapM infer tys
--  (args , ret) = splitAt (length tys - 1) tys
--  mergeTT :: Bind -> Bind -> Bind
--  mergeTT b1 b2
--    E eta -> \case
--      E eta2 -> 
--    T ty
--    B term -> error $ "terms in tyArrow"
    _ --foldr mergeTT ret $ mapM infer tys
  x -> error $ "top not ready for " ++ show x

-- Biunification handles constraints of the form t+ <= t- by substitution
-- Atomic: (join/meet a type to the var)
-- a  <= t- solved by [m- b = a n [b/a-]t- /a-] 
-- t+ <= a  solved by [m+ b = a u [b/a+]t+ /a+] 
-- a  <= c  solved by [m- b = a n [b/a-]c  /a-] -- (or equivalently,  [a u b /b+])
-- SubConstraints:
-- (t1- -> t1+ <= t2+ -> t2-) = {t2+ <= t1- , t+ <= t2-}
biSub_ a b = trace ("bisub: " ++ show a ++ " <--> " ++ show b) biSub a b
biSub :: TyPlus -> TyMinus -> TCEnv Bool
-- lattice top and bottom
biSub [] _ = pure False
biSub _ [] = pure False
-- atomic constraints
biSub [THVar p] m = (biSubs . (ix p) . mSub %= (m ++) ) *> pure True -- includes var1 <= var2 case
biSub p [THVar m] = (biSubs . (ix m) . pSub %= (p ++) ) *> pure True
-- lattice subconstraints
biSub (p1:p2:p3) m = biSub [p1] m *> biSub (p2:p3) m
biSub p (m1:m2:m3) = biSub p [m1] *> biSub p (m2:m3)
-- head constructor subconstraints
biSub [THArrow args1 ret1] [THArrow args2 ret2] = zipWithM biSub args2 args1 *> biSub ret1 ret2
biSub [THRec i p] m = _
biSub p [THRec i m] = _

-- primitives
biSub [THPrim p1] [THPrim p2] = if p1 == p2 then pure True else failBiSub p1 p2

-- between lattice components
-- type function
biSub h@[THHigher uni] [THArrow x ret] = biSub h ret

-- lattice components mismatch; biSub is partial, since subtyping isn't defined between all type components
biSub a b = failBiSub a b

failBiSub a b = error $ "failed bisub: " ++ show a ++ "<-->" ++ show b --pure False

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
check :: [TyHead] -> Set -> TCEnvState -> Bool
check gotRaw expRaw delta = let
  gotTy = reduceType gotRaw ; expTy = reduceType expRaw
  _check ty = True
  in  all _check gotTy

-- handle intricacies of merging types with terms
-- to distinguish indexed type and typecase, we need to know the return type
-- Int : T0 -> T1 -- indexed
-- TC  : T1 -> T0 -- type case, returns a term
-- TODO merge of lattice components ?
ttApp :: Expr -> Expr -> Expr
ttApp a b = case (a , b) of
  (Core t ty , Core t2 ty2) -> case t of
    App f x -> Core (App f (x++[t2])) [] -- dont' forget to set the return type
    _       -> Core (App t [t2])      []
  (Ty s , Ty s2)            -> Ty $ [THIxType s s2]       -- type index
  (Ty s , c@(Core t ty))    -> Ty $ [THIxTerm s (t , ty)] -- term index
  (c@(Core t ty) , Ty s)    -> Ty $ [THEta  t s] -- only valid if c is an eta expansion

typeOf :: Bind -> [TyHead]
typeOf = \case
  WIP -> error "panic: impossibly found wip bound after inference"
  B args  term ty -> ty
  T targs set     -> set

mkTcFailMsg gotTerm gotTy expTy =
  ("subsumption failure:"
  ++ "\nExpected: " ++ show expTy
  ++ "\nGot:      " ++ show gotTy
-- ++ "\n" ++ show (unVar gotTy) ++ " <:? " ++ show expected
  ++ "\nIn the expression: " ++ show gotTy
  )

typeOfLit = \case
  String{}   -> THPrim $ PtrTo (PrimInt 8) --"CharPtr"
  Array{}    -> THPrim $ PtrTo (PrimInt 8) --"CharPtr"
  PolyInt{} -> THPrim (PrimInt 32)
  x -> error $ "littype: " ++ show x
--  _ -> numCls

eqTyHead a b = kindOf a == kindOf b
kindOf THPrim{}  = KPrim
kindOf THAlias{} = _ -- have to deref it
kindOf THVar{}   = KVar
kindOf THArrow{} = KArrow
kindOf THRec{}   = _
kindOf THData{}  = KData
