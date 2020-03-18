-- Type judgements: checking and inferring
-- See "Algebraic subtyping" by Stephen Dolan <https://www.cl.cam.ac.uk/~sd601/thesis.pdf>

module BiUnify where
import Prim
import qualified ParseSyntax as P
import CoreSyn as C
import TCState
import PrettyCore
import qualified CoreUtils as CU
import DesugarParse
import Externs

import qualified Data.Vector.Mutable as MV -- mutable vectors
import qualified Data.Vector as V
import qualified Data.Map as M
import qualified Data.IntMap as IM
import qualified Data.Text as T
import Data.Functor
import Control.Monad
import Control.Applicative
import Control.Monad.Trans.State.Strict
import Data.List --(foldl', intersect)
import Control.Lens

import Debug.Trace
d_ x   = trace (clYellow (show x))
did_ x = d_ x x

-- test1 x = x.foo.bar{foo=3}

judgeModule :: P.Module -> V.Vector Bind
judgeModule pm = let
  nBinds = length $ pm ^. P.bindings
  (externVars , externBinds) = resolveImports pm
  start = TCEnvState
    { _pmodule  = pm
    , _noScopes = externVars
    , _externs  = traceShowId externBinds
    , _biSubs   = V.empty
    , _wip      = V.replicate nBinds WIP
    }
  go  = mapM_ judgeBind [0 .. nBinds-1]
  end = execState go start
  in end ^. wip

-- Add fresh bisubs for lambda-bound vars and infer an expression
-- Used by lambda-abs and case
withNewBiSubs :: Int -> P.TT -> TCEnv (Expr , V.Vector Type)
withNewBiSubs nArgs tt = do
  biSubLen <- V.length <$> use biSubs
  let genFn i = let x = i + biSubLen in BiSub [THVar x] [THVar x]
  biSubs %= (V.++ V.generate nArgs genFn)
  expr <- infer tt
  (bis , argSubs) <- (\v -> V.splitAt (biSubLen) v) <$> use biSubs
  biSubs .= bis
  pure (expr , _mSub <$> argSubs)

judgeBind :: IName -> TCEnv Bind
 = \bindINm -> (V.! bindINm) <$> use wip >>= \t -> case t of
  BindTerm arNms term ty  -> pure t
  BindType tArgs ty       -> pure t
  WIP -> do
    P.FunBind hNm matches tyAnn <- (!! bindINm) <$> use (id . pmodule . P.bindings)
    let (args , tt) = matches2TT matches
        nArgs = length args
    (expr , argTys) <- withNewBiSubs nArgs tt
--  case tyAnn of
--    Nothing -> pure expr
--    Just t  -> check res tyAnn <$> use wip -- mkTCFailMsg e tyAnn res
    let newBind = case expr of
          Core x t -> if nArgs == 0
            then  BindTerm args x t
            else  BindTerm args x [THArrow (V.toList argTys) t]
          Ty   t   -> BindType [] t -- args ? TODO
    wip %= V.modify (\v->MV.write v bindINm newBind)
    pure newBind

infer :: P.TT -> TCEnv Expr
 = let
 getArgTy  = \case
   Core x ty -> ty
   Ty t      -> [THHigher 1]     -- type of types
   Set u t   -> [THHigher (u+1)]
 in \case
  P.WildCard -> _
  -- vars : lookup in the environment
  P.Var v -> case v of
    P.VBind b   ->    -- polytype env
      judgeBind b <&> \case { BindTerm args e ty
        -> Core (Var $ VBind b) ty }
    P.VLocal l  -> do -- monotype env (fn args)
      ty <- _pSub . (V.! l) <$> use biSubs
      pure $ Core (Var $ VArg l) ty
    P.VExtern i -> do
      extIdx <- (V.! i)      <$> use noScopes
      expr   <- (V.! extIdx) <$> use externs
      pure expr
    x -> error $ show x

  -- APP: f : [Df-]ft+ , Pi ^x : [Df-]ft+ ==> e2:[Dx-]tx+
  -- |- f x : biunify [Df n Dx]tx+ under (tf+ <= tx+ -> a)
  -- * introduce a typevar 'a', and biunify (tf+ <= tx+ -> a)
  P.App f args -> let
    ttApp :: Expr -> Expr -> Expr
    ttApp a b = case (a , b) of
      (Core t ty , Core t2 ty2) -> case t of
        App f x -> Core (App f (x++[t2])) [] -- dont' forget to set the return type
        _       -> Core (App t [t2])      []
      (Ty s , Ty s2)            -> Ty $ [THIxType s s2]       -- type index
      (Ty s , c@(Core t ty))    -> Ty $ [THIxTerm s (t , ty)] -- term index
      (c@(Core t ty) , Ty s)    -> Ty $ [THEta t s] -- only valid if c is an eta expansion
    in do
    f'   <- infer f
    args'<- mapM infer args
    retTy <- do
      idx <- V.length <$> use biSubs
      biSubs %= (`V.snoc` BiSub [THVar idx] [THVar idx]) -- bisub for return type
      biSub_ (getArgTy f') [THArrow (getArgTy <$> args') [THVar idx]]
      (_pSub . (V.! idx) <$> use biSubs) <* (biSubs %= V.init)
    pure $ case foldl' ttApp f' args' of
      Core f _ -> Core f retTy
      t -> t

  -- Record
  P.Cons construct   -> do -- assign arg types to each label (cannot fail)
    let (fields , rawTTs) = unzip construct
    exprs <- mapM infer rawTTs
    let (tts , tys) = unzip $ (\case { Core t ty -> (t , ty) }) <$> exprs
    pure $ Core (Cons (M.fromList $ zip fields tts)) [THProd (M.fromList $ zip fields tys)]

  P.Proj tt field -> do -- biunify (t+ <= {l:a})
    recordTy <- infer tt
    retTy <- do
      idx <- V.length <$> use biSubs
      biSubs %= (`V.snoc` newBiSub)
      biSub_ (getArgTy recordTy) [THProd (M.singleton field [THVar idx])]
      (_pSub . (V.! idx) <$> use biSubs) <* (biSubs %= V.init)
    pure $ case recordTy of
      Core f _ -> Core (Proj f field) retTy
      t -> t

  -- Sum
  P.Label l tt -> do
    (t , ty) <- (\case { Core t ty -> (t , ty) }) <$> infer tt
    pure $ Core (Label l t) [THSum $ M.fromList [(l , ty)]]

  P.Match alts -> do
    -- * find the type of the sum type being deconstructed
    -- * find the type of it's alts (~ lambda abstractions)
    -- * type of Match is (sumTy -> Join altTys)
    let (labels , patterns , rawTTs) = unzip3 alts
    (exprs , vArgTys) <- unzip <$> mapM (withNewBiSubs 1) rawTTs
    let (altTTs , altTys) = unzip
          $ (\case { Core t ty -> (t , ty) }) <$> exprs
        argTys  = (\[x]->x) . V.toList <$> vArgTys
        sumTy   = [THSum . M.fromList $ zip labels argTys]
        matchTy = [THArrow [sumTy] (concat $ altTys)]
    pure $ Core (Match (M.fromList $ zip labels altTTs) Nothing) matchTy

  P.MultiIf branches -> do -- Bool ?
    let (rawConds , rawAlts) = unzip branches
        boolTy = getPrimIdx "Bool" & \case
          { Just i->THExt i; Nothing->error "panic: \"Bool\" not in scope" }
        addBool = doSub (-1) boolTy
    condExprs <- mapM infer rawConds
    alts      <- mapM infer rawAlts
    let retTy = foldr1 mergeTypes (getArgTy <$> alts) :: [TyHead]
        ifTy = [THArrow (addBool . getArgTy <$> condExprs) retTy]
        e2t (Core e ty) = e
    pure $ Core (MultiIf (zip (e2t<$>condExprs) (e2t<$>alts))) ifTy
    _

  ---------------------
  -- term primitives --
  ---------------------
  P.Lit l  -> pure $ Core (Lit l) [typeOfLit l] -- the type of primitives is non-negotiable

  ---------------------
  -- type primitives --
  ---------------------
  P.TyLit primTy -> pure $ Ty [THPrim primTy]

  -- arrows may contain types or eta-expansions
  P.TyArrow tys  -> do -- type given to an Abs
    arrows <- mapM infer tys
    _ --foldr mergeTT ret $ mapM infer tys

  -- desugar
  P.InfixTrain lArg train -> infer $ resolveInfixes _ lArg train
  x -> error $ "not ready for tt: " ++ show x

-- Biunification handles constraints of the form t+ <= t- by substitution
-- Atomic: (join/meet a type to the var)
-- a  <= t- solved by [m- b = a n [b/a-]t- /a-] 
-- t+ <= a  solved by [m+ b = a u [b/a+]t+ /a+] 
-- a  <= c  solved by [m- b = a n [b/a-]c  /a-] -- (or equivalently,  [a u b /b+])
-- SubConstraints:
-- (t1- -> t1+ <= t2+ -> t2-) = {t2+ <= t1- , t+ <= t2-}
biSub_ a b = trace ("bisub: " ++ show a ++ " <==> " ++ show b) biSub a b
biSub :: TyPlus -> TyMinus -> TCEnv ()
biSub a b = case (a , b) of
  -- lattice top and bottom
  ([] ,  _) -> pure ()
  (_  , []) -> pure ()
  -- atomic constraints
  ([THVar p] , m) -> (biSubs . (ix p) . mSub %= foldr (doSub p) m )
  (p , [THVar m]) -> (biSubs . (ix m) . pSub %= foldr (doSub m) p )
  ([THPrim p1] , [THPrim p2]) -> when (p1 /= p2) (failBiSub p1 p2)

  -- lattice subconstraints
  ((p1:p2:p3) , m) -> biSub [p1] m *> biSub (p2:p3) m
  (p , (m1:m2:m3)) -> biSub p [m1] *> biSub p (m2:m3)
  (p , [THExt i])  -> biSub p =<< tyExpr . (V.! i) <$> use externs
  ([THExt i] , m)  -> (`biSub` m) =<< tyExpr . (V.! i) <$> use externs

  -- basic head constructor subconstraints
  ([THArrow args1 ret1] , [THArrow args2 ret2]) -> zipWithM biSub args2 args1 *> biSub ret1 ret2
  -- record: labels in the first must all be in the second
  ([THProd fields1] , [THProd fields2]) -> let
    go (l , ttm) = case M.lookup l fields1 of
      Nothing  -> error $ "label not present"
      Just ttp -> biSub ttp ttm --covariant
    in mapM_ go (M.toList fields2)

  ([THRec i p] , m) -> _
  (p , [THRec i m]) -> _

  (h@[THHigher uni] , [THArrow x ret]) -> biSub h ret

  -- lattice components without subtyping relation
  (a , b) -> failBiSub a b

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
-- additionally, subsumption <===> equivalence of typing schemes
-- ie. to decide [d1]t1 <= [d2]t2, we check alpha-equivalence of [d1 n d2]t1 u t2 with [d2]t2
check :: [TyHead] -> Set -> TCEnvState -> Bool
check gotRaw expRaw delta = let
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

eqTyHead a b = kindOf a == kindOf b
kindOf = \case
  THPrim{}  -> KPrim
  THAlias{} -> _ -- have to deref it
  THVar{}   -> KVar
  THArrow{} -> KArrow
  THRec{}   -> _
  _ -> KAny

mergeTypes :: [TyHead] -> [TyHead] -> [TyHead]
mergeTypes l1 l2 = foldr (\a b -> doSub (-1) a b) l2 l1

-- merge a tyhead into a bisub ; remove the typevar if resolved
-- mu binders ?
-- doSub i = (:)
doSub :: Int -> TyHead -> [TyHead] -> [TyHead]
doSub i (THVar v) [] = if i == v then [] else [THVar v]
doSub i newTy [] = [newTy]
doSub i newTy (ty:tys) = if eqTyHead newTy ty
  then mergeTyHead i newTy ty ++ tys
  else (ty : doSub i newTy tys)

mergeTyHead :: Int -> TyHead -> TyHead -> [TyHead]
mergeTyHead int t1 t2 = let join = [t1 , t2] in case join of
  [THPrim a , THPrim b]   -> if a == b then [t1] else join
  [THVar a , THVar b]     -> if a == b then [t1] else join
  [THAlias a , THAlias b] -> if a == b then [t1] else join
  [THSum a , THSum b]   -> _
  [THProd a , THProd b] -> _
--[THArrow a , THArrow b] -> _
  _ -> join
