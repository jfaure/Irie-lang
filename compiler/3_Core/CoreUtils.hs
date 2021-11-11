module CoreUtils where
----------------------------------------------------
-- Various utility functions operating on CoreSyn --
----------------------------------------------------
-- Any function that could be given in CoreSyn directly is found here
import CoreSyn
import ShowCore()
import PrettyCore
import Prim
import qualified Data.IntMap as IM
--import qualified Data.IntSet as IS

nullLattice pos = \case
  [] -> if pos then [THBot] else [THTop]
  t  -> t

mkTHArrow args retTy = let singleton x = [x] in mkTyArrow (singleton <$> args) (singleton retTy)
mkTyArrow args retTy = [THTyCon $ THArrow args retTy]

-- substitute all pi bound variables for new typevars;
-- otherwise guarded debruijn vars won't be biunified on contact with TVar
-- ; ie. TVar slots may contain stale debruijns, after which the pi-binder context is lost
-- TODO record and sum type also
substFreshTVars tvarStart = Prelude.map $ let
  r = substFreshTVars tvarStart
  in \case
  THBound i -> THVar (tvarStart + i)
  THMu m t  -> THMu m $ r t
  THTyCon t -> THTyCon $ case t of
    THArrow as ret -> THArrow (r <$> as) (r ret)
    THProduct as   -> THProduct $ r <$> as
    THTuple as     -> THTuple   $ r <$> as
    THSumTy as     -> THSumTy   $ r <$> as
--THMuBound m -> THMuBound m
--THTop -> THTop
--THBot -> THBot
--THExt i -> THExt i
  t -> t
--t -> error $ show t

getArrowArgs = \case
  [THTyCon (THArrow as r)] -> (as , r)
  [THBi i t] -> getArrowArgs t
  t -> trace ("not a function type: " <> prettyTyRaw t) ([] , t)

-- appendArrowArgs [] = identity
-- appendArrowArgs args = \case
--   [THTyCon (THArrow as r)] -> [THTyCon $ THArrow (as ++ args) r]
--   [THPi (Pi p t)]   -> [THPi (Pi p $ appendArrowArgs args t)]
--   [THSi (Pi p t) _] -> [THPi (Pi p $ appendArrowArgs args t)]
--   [THBi i t] -> [THBi i $ appendArrowArgs args t]
--   x -> [THTyCon $ THArrow args x]

prependArrowArgs [] = identity
prependArrowArgs args = \case
  [THTyCon (THArrow as r)] -> [THTyCon $ THArrow (args ++ as) r]
  [THPi (Pi p t)]   -> [THPi (Pi p $ prependArrowArgs args t)]
  [THSi (Pi p t) _] -> [THPi (Pi p $ prependArrowArgs args t)]
  [THBi i t] -> [THBi i $ prependArrowArgs args t]
  x -> [THTyCon $ THArrow args x]

onRetType :: (Type -> Type) -> Type -> Type
onRetType fn = \case
  [THTyCon (THArrow as r)] -> [THTyCon $ THArrow as (onRetType fn r)]
  [THPi (Pi p t)] -> [THPi (Pi p $ onRetType fn t)]
  [THMu m t] -> [THMu m (onRetType fn t)]
  x -> fn x
--x -> x --onRetType fn <$> x

getRetTy = \case
  [THTyCon (THArrow _ r)] -> getRetTy r -- currying
  [THPi (Pi ps t)] -> getRetTy t
  [THBi i t] -> getRetTy t
  x -> x

isTyCon = \case
 THTyCon{} -> True
 _         -> False

isArrowTy = \case
  [THTyCon (THArrow{})] -> True
  [THPi (Pi p t)] -> isArrowTy t
  [THBi i t] -> isArrowTy t
  [THSi (Pi p t) _] -> isArrowTy t
  x -> False

flattenArrowTy ty = let
  go = \case
    [THTyCon (THArrow d r)] -> let (d' , r') = go r in (d ++ d' , r')
    t -> ([] , t)
  in (\(ars,r) -> [THArrow ars r]) . go $ ty

tyOfTy :: Type -> Type
tyOfTy t = case t of
  [] -> _
  [THRecSi f ars] -> let
    arTys = take (length ars) $ repeat [THSet 0]
    uni = maximum $ (\case { [THSet n] -> n ; x -> 0 }) <$> arTys
    in [THTyCon $ THArrow arTys [THSet uni]]
  [t] -> [THSet 0]
  t  -> panic $ "multiple types: " <> show t

tyExpr = \case -- expr found as type, (note. raw exprs cannot be types however)
  Ty t -> Just t
  expr -> Nothing --error $ "expected type, got: " ++ show expr

tyOfExpr  = \case
  Core x ty -> ty
  Ty t      -> tyOfTy t
  PoisonExpr-> []
  m@MFExpr{}-> error $ "unexpected mfexpr: " <> show m

-- expr2Ty :: _ -> Expr -> TCEnv s Type
-- Expression is a type (eg. untyped lambda calculus is both a valid term and type)
expr2Ty judgeBind e = case e of
 Ty x -> pure x
 Core c ty -> case c of
   Var (VBind i) -> pure [THRecSi i []]
   Var (VArg x)  -> pure [THVar x] -- TODO ?!
   App (Var (VBind fName)) args -> pure [THRecSi fName args]
   x -> error $ "raw term cannot be a type: " ++ show e
 PoisonExpr -> pure [THPoison]
 x -> error $ "raw term cannot be a type: " ++ show x

bind2Expr = \case
  BindOK e    -> e

------------------------
-- Type Manipulations --
------------------------
eqTyHead a b = kindOf a == kindOf b
kindOf = \case
  THPrim{}  -> KPrim
  THVar{}   -> KVar
  THTyCon t -> case t of
    THArrow{}   -> KArrow
    THProduct{} -> KProd
    THSumTy{}   -> KSum
    THTuple{}   -> KTuple
    THArray{}   -> KArray
  THBound{} -> KBound
  THMuBound{} -> KRec
  THMu{} -> KRec
  _ -> KAny

mergeTypes :: [TyHead] -> [TyHead] -> [TyHead]
--mergeTypes l1 l2 = concat $ foldr doSub [] <$> (groupBy eqTyHead (l1 ++ l2))
mergeTypes l1 l2 = let
  cmp a b = case (a,b) of
    (THBound a' , THBound b') -> compare a' b'
    _ -> (kindOf a) `compare` (kindOf b)
  in foldr doSub [] (sortBy cmp $ l2 ++ l1)

mergeTyHeadType = doSub
-- add head constructors, transitions and flow edges
doSub :: TyHead -> [TyHead] -> [TyHead]
doSub (THMu x (t:ts)) [] = [THMu x (doSub t ts)]
doSub newTy [] = [newTy]
doSub newTy (ty:tys) = mergeTyHead newTy ty ++ tys
--if eqTyHead newTy ty
--then mergeTyHead newTy ty ++ tys
--else (ty : doSub newTy tys)

-- generally mergeing depends on polarities. We only merge equal types (typevars mostly) here
-- Note output(+) (%i1 | %i32) is (%i1) by subtyping, but codegen needs to know the 'biggest' type
-- Also, The 'biggest' type is not always the negative merge
mergeTyHead :: TyHead -> TyHead -> [TyHead]
mergeTyHead t1 t2 = -- trace (show t1 ++ " ~~ " ++ show t2) $
  let join = [t1 , t2]
      zM  :: Semialign f => f [TyHead] -> f [TyHead] -> f [TyHead]
      zM  = alignWith (these identity identity mergeTypes)
  in case join of
  [THMu a t1 , THMu b t2] | a == b -> [THMu a (t1 `mergeTypes` t2)]
--[THMu x t1 , THMuBound y] | x == y -> [THMu x t1]
--[THMuBound y , THMu x t1] | x == y -> [THMu x t1]
  [THMu x t1 , THMuBound y] -> {-[THMu x t1] -} [THMuBound y]
  [THMuBound y , THMu x t1] -> {-[THMu x t1] -} [THMuBound y]
  [THMu x t1 , t2] -> [THMu x (doSub t2 t1)]
  [t2 , THMu x t1] -> [THMu x (doSub t2 t1)]
  [THTop , THTop] -> [THTop]
  [THBot , THBot] -> [THBot]
  [THSet a , THSet b] -> [THSet $ max a b]
  [THPrim a , THPrim b]  -> if a == b then [t1] else case (a,b) of
--  (PrimInt x , PrimInt y) -> [THPrim $ PrimInt $ max x y]
    (PrimBigInt , PrimInt y) -> [THPrim $ PrimBigInt]
    (PrimInt y , PrimBigInt) -> [THPrim $ PrimBigInt]
    _ -> join
  [THMuBound a , THMuBound b] -> if a == b then [t1] else join
  [THBound a , THBound b]     -> if a == b then [t1] else join
  [THVar a , THVar b]         -> if a == b then [t1] else join
  [THExt a , THExt  b]        -> if a == b then [t1] else join
  [THTyCon t1 , THTyCon t2]   -> case [t1,t2] of -- TODO depends on polarity (!)
    [THSumTy a   , THSumTy b]   -> [THTyCon $ THSumTy   $ IM.unionWith mergeTypes a b]
    [THProduct a , THProduct b] -> [THTyCon $ THProduct $ IM.unionWith mergeTypes a b]
    [THTuple a , THTuple b]     -> [THTyCon $ THTuple   $ zM a b]
    [THArrow d1 r1 , THArrow d2 r2] | length d1 == length d2 -> [THTyCon $ THArrow (zM d1 d2) (mergeTypes r1 r2)]
    x -> join
  [THFam f1 a1 i1 , THFam f2 a2 i2] -> [THFam (mergeTypes f1 f2) (zM a1 a2) i1] -- TODO merge i1 i2!
  [THPi (Pi b1 t1) , THPi (Pi b2 t2)] -> [THPi $ Pi (b1 ++ b2) (mergeTypes t1 t2)]
  [THPi (Pi b1 t1) , t2] -> [THPi $ Pi b1 (mergeTypes t1 [t2])]
  [t1 , THPi (Pi b1 t2)] -> [THPi $ Pi b1 (mergeTypes [t1] t2)]
  _ -> join
