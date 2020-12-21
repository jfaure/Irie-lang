module CoreUtils where
----------------------------------------------------
-- Various utility functions operating on CoreSyn --
----------------------------------------------------
import Prim
import CoreSyn
import PrettyCore
import Data.List
import qualified Data.Vector as V

-- Freevars ignored ?
getArgs :: Expr -> [(IName , Type)] = \case
  CoreFn args _ _ _ -> args
  x -> []

isArrowTy = \case
  [THArrow{}] -> True
  [THPi (Pi p t)] -> isArrowTy t
  [THSi (Pi p t) _] -> isArrowTy t
  x -> False

getRetTy = \case
  [THArrow _ r] -> getRetTy r -- currying
  [THPi (Pi ps t)] -> getRetTy t
  x -> x

flattenArrowTy ty = let
  go = \case
    [THArrow d r] -> let (d' , r') = go r in (d ++ d' , r')
    t -> ([] , t)
  in (\(ars,r) -> [THArrow ars r]) . go $ ty

tyOfTy t = case t of
  [] -> _
  [THRecSi f ars] -> let
    arTys = take (length ars) $ repeat [THSet 0]
    uni = maximum $ (\case { [THSet n] -> n ; x -> 0 }) <$> arTys
    in [THArrow arTys [THSet uni]]
  [t] -> [THSet 0]
  t  -> error $ "multiple types: " ++ show t

tyOfExpr  = \case
  Core x ty -> ty
  CoreFn _ _ _ ty  -> ty
  ExtFn _nm ty -> ty
  Ty t      -> tyOfTy t
  Fail e    -> []

-- expr2Ty :: _ -> Expr -> TCEnv s Type
-- Expression is a type (eg. untyped lambda calculus is both a valid term and type)
expr2Ty judgeBind e = case e of
 Ty x -> pure x
 Core c ty -> case c of
   Var (VBind x) -> pure [THRec x]
   Var (VArg x)  -> pure [THArg x] -- TODO ?!
   App (Var (VBind fName)) args -> pure [THRecSi fName args]
   x -> error $ "raw term cannot be a type: " ++ show e
 x -> error $ "raw term cannot be a type: " ++ show x

getTypeIndexes = \case
  [THFam t args ixs] -> ixs
  [THRecSi m ixs] -> (`Core` []) <$> ixs
  [THPi (Pi b ty)] -> getTypeIndexes ty
  x -> []

--zipWithPad :: a -> b -> (a->b->c) -> [a] -> [b] -> [c]
--zipWithPad a b f = go where
--  go [] y = zipWith f (repeat a) y
--  go x [] = zipWith f x (repeat b)
--  go (x:xs) (y:ys) = f x y : go xs ys

mergeIndex :: Expr -> Expr -> Expr
mergeIndex = _

bind2Expr = \case { BindOK e -> e }

------------------------
-- Type Manipulations --
------------------------
eqTyHead a b = kindOf a == kindOf b
kindOf = \case
  THPrim{}  -> KPrim
  THVar{}   -> KVar
  THArrow{} -> KArrow
  _ -> KAny


mergeTypes :: [TyHead] -> [TyHead] -> [TyHead]
mergeTypes l1 l2 = foldr doSub l2 l1

-- add head constructors, transitions and flow edges
doSub :: TyHead -> [TyHead] -> [TyHead]
doSub newTy [] = [newTy]
doSub newTy (ty:tys) = if eqTyHead newTy ty
  then mergeTyHead newTy ty ++ tys
  else (ty : doSub newTy tys)

mergeTyHead :: TyHead -> TyHead -> [TyHead]
mergeTyHead t1 t2 = -- trace (show t1 ++ " ~~ " ++ show t2) $
  let join = [t1 , t2]
      zM = zipWith mergeTypes
  in case join of
  [THSet a , THSet b] -> [THSet $ max a b]
  [THPrim a , THPrim b]  -> if a == b then [t1] else join
  [THVar a , THVar b]    -> if a == b then [t1] else join
  [THRec a , THRec b]    -> if a == b then [t1] else join
  [THExt a , THExt  b]   -> if a == b then [t1] else join
--  [THAlias a , THAlias b] -> if a == b then [t1] else join
  [THSum a , THSum b]     -> [THSum   $ union a b] --[THSum (M.unionWith mergeTypes a b)]
  [THSplit a , THSplit b] -> [THSplit $ union a b] --[THSum (M.unionWith mergeTypes a b)]
  [THProd a , THProd b]   -> [THProd $ intersect a b] -- [THProd (M.unionWith mergeTypes a b)]
  [THArrow d1 r1 , THArrow d2 r2]
    | length d1 == length d2 -> [THArrow (zM d1 d2) (mergeTypes r1 r2)]
  [THFam f1 a1 i1 , THFam f2 a2 i2] -> [THFam (mergeTypes f1 f2) (zM a1 a2) i1] -- TODO merge i1 i2!
  [THPi (Pi b1 t1) , THPi (Pi b2 t2)] -> [THPi $ Pi (b1 ++ b2) (mergeTypes t1 t2)]
  [THPi (Pi b1 t1) , t2] -> [THPi $ Pi b1 (mergeTypes t1 [t2])]
  [t1 , THPi (Pi b1 t2)] -> [THPi $ Pi b1 (mergeTypes [t1] t2)]
--[THRecSi r1 a1 , THRecSi r2 a2] -> if r1 == r2
--  then [THRecSi r1 (zipWith mergeTypes a1 a2)]
--  else join
  _ -> join

-- substitute type variables
-- TODO guard against loop
rmTypeVars :: V.Vector BiSub -> V.Vector BiSub -> Type -> Type
rmTypeVars tyVars argVars = foldl1 mergeTypes . map (rmTypeVarsSingle tyVars argVars)
--rmTypeVarsSingle :: V.Vector Bisub -> V.Vector BiSub -> Type -> Type
rmTypeVarsSingle tyVars argVars = let
  rmTypeVarsSingle' = rmTypeVarsSingle tyVars argVars
  rmTypeVars'  = rmTypeVars tyVars argVars
  in \case
  THVar v -> _pSub $ tyVars  V.! v
  THRec r -> _pSub $ tyVars  V.! r
  THArg a -> _mSub $ argVars V.! a
  
  THArrow    ars ret -> [THArrow (rmTypeVars' <$> ars) (rmTypeVars' ret)]
  t -> [t]
--THPi Pi -- dependent function space. Always implicit, for explicit, write `∏(x:_) x -> Z`
--THSi Pi (IM.IntMap Expr) -- (partial) application of pi type
--THRecSi IName [Term]     -- basic case when parsing a definition; also a valid CoreExpr
--THFam Type [Type] [Expr] -- type of things it can index, and things indexing it (both can be [])
