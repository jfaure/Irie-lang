-- Type judgements: checking and inferring
-- For an introduction to these concepts,
-- see "Algebraic subtyping" by Stephen Dolan <https://www.cl.cam.ac.uk/~sd601/thesis.pdf>

module Infer where
import Prim
import BiUnify
import qualified ParseSyntax as P
import CoreSyn as C
import TCState
import PrettyCore
import qualified CoreUtils as CU
import DesugarParse
import Externs

import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV -- mutable vectors
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

-- test1 x = x.foo.bar{foo=3}

judgeModule :: P.Module -> V.Vector Bind
judgeModule pm = let
  nBinds = length $ pm ^. P.bindings
  (externVars , externBinds) = resolveImports pm
  start         = TCEnvState
    { _pmodule  = pm
    , _noScopes = externVars
    , _externs  = trace (clCyan $ show externBinds) externBinds
    , _biSubs   = V.empty
    , _polyVars = 0
    , _wip      = V.replicate nBinds WIP
    }
  go  = judgeBind `mapM_` [0 .. nBinds-1]
  in execState go start ^. wip

withBiSubs :: Int -> (Int->TCEnv a) -> TCEnv (a , BiSubs)
withBiSubs n action = do
  biSubLen <- V.length <$> use biSubs
  let genFn i = let tv = [THVar $ i + biSubLen] in BiSub tv tv
  biSubs %= (V.++ V.generate n genFn)
  ret <- action biSubLen

  argSubs <- V.drop biSubLen <$> use biSubs

--bis <- use biSubs
--bis' <- solveBiSub `V.imapM` bis
--let (oldBis , argSubs) = V.splitAt biSubLen bis'
--biSubs .= oldBis
  pure (ret , argSubs)

--solveBiSub i (BiSub a b) = let
--  s = solveTVars bis
--  in BiSub <$> s _pSub i a <*> s _mSub i b

-- solveTVars: replace/remove all THVars
-- unresolved THVars become implicit type args (~= forall)
--solveTVars :: (BiSub->Type)-> Int -> Type -> TCEnv Type
--solveTVars getTy i ty =
--  case ty of
--  [THVar t] -> if i /= t
--    then getTy <$> solveBiSub i =<< (V.! t) <$> use biSubs
--    else do
--      p <- use polyVars
--      polyVars += 1
----    biSubs . ix i . pSub %= [THImplicit p]
--      pure [THImplicit p]
--  t -> pure t

judgeBind :: IName -> TCEnv Bind
 = \bindINm -> (V.! bindINm) <$> use wip >>= \t -> case t of
  BindTerm arNms term ty  -> pure t
  BindType tArgs ty       -> pure t
  WIP -> do
    P.FunBind hNm matches tyAnn <- (!! bindINm) <$> use (id . pmodule . P.bindings)
    let (args , tt) = matches2TT matches
        nArgs = length args
    (expr , argSubs) <- withBiSubs nArgs (\_ -> infer tt)
    let argTys = _mSub <$> argSubs
--  case tyAnn of
--    Nothing -> pure expr
--    Just t  -> check res tyAnn <$> use wip
--      -- mkTCFailMsg e tyAnn res
    let newBind = case expr of
          Core x t -> do
            if nArgs == 0
              then BindTerm args x t
              else BindTerm args x [THArrow (V.toList argTys) t]
          Ty   t   -> BindType [] t -- args ? TODO
    wip %= V.modify (\v->MV.write v bindINm newBind)
    pure newBind

infer :: P.TT -> TCEnv Expr
 = let
 -- expr found in type context (should be a type or var)
 -- in product types, we fold ttApp to collect dependent sum/pi types
 yoloGetTy :: Expr -> Type
 yoloGetTy = \case
   Ty x -> x
   Core (Var v) typed -> case v of
     VBind i -> [THAlias i]
     VArg  i -> [THArg i]
     VExt  i -> [THExt i]
   x -> error $ "type expected: " ++ show x
 getArgTy  = \case
   Core x ty -> ty
   Ty t      -> [THHigher 1]     -- type of types
   Set u t   -> [THHigher (u+1)]
 in \case
  P.WildCard -> _
  -- vars : lookup in appropriate environment
  P.Var v -> case v of
    P.VBind b   ->    -- polytype env
      judgeBind b <&> \case { BindTerm args e ty
        -> Core (Var $ VBind b) ty }
    P.VLocal l  -> do -- monotype env (fn args)
      ty <- _pSub . (V.! l) <$> use biSubs
      pure $ Core (Var $ VArg l) ty
    P.VExtern i -> do
      extIdx <- (V.! i) <$> use noScopes
      (V.! extIdx) <$> use externs
    x -> error $ show x

  -- APP: f : [Df-]ft+ , Pi ^x : [Df-]ft+ ==> e2:[Dx-]tx+
  -- |- f x : biunify [Df n Dx]tx+ under (tf+ <= tx+ -> a)
  -- * introduce a typevar 'a', and biunify (tf+ <= tx+ -> a)
  P.App f args -> let
    ttApp :: Expr -> Expr -> Expr
    ttApp a b = case (a , b) of
      (Core t ty , Core t2 ty2) -> case t of
        App f x -> Core (App f (x++[t2])) [] -- dont' forget to set the return type later !
        _       -> Core (App t [t2])      []
      (Ty s , Ty s2)         -> Ty$ [THIxType s s2]       -- type index
      (Ty s , c@(Core t ty)) -> Ty$ [THIxTerm s (t , ty)] -- term index
      (c@(Core t ty) , Ty s) -> Ty$ [THEta t s] -- only valid if c is an eta expansion
    in do
    f'    <- infer f
    args' <- infer `mapM` args
    case f' of
      -- special case: Array Literal
      Core (Lit l) ty -> do
        let getLit (Core (Lit l) _) = l
            argLits = getLit <$> args'
        pure $ Core (Lit . Array $ l : argLits) [THArray ty]
        -- TODO merge (join) all tys ?

      -- special case: "->" THArrow tycon. ( : Set->Set->Set)
      Core (Instr ArrowTy) _ty -> let
        getTy t = yoloGetTy t --case yoloGetTy t of { Ty t -> t }
        (ars, [ret]) = splitAt (length args' - 1) (getTy <$> args')
        in pure $ Ty [THArrow ars ret]

      -- normal function app
      f' -> do
        retTy <- do
          _pSub . (V.! 0) . snd <$> withBiSubs 1 (\idx ->
            biSub_ (getArgTy f') [THArrow (getArgTy <$> args') [THVar idx]])
        pure $ case foldl' ttApp f' args' of
          Core f _ -> Core f retTy
          t -> t

  -- Record
  P.Cons construct   -> do -- assign arg types to each label (cannot fail)
    let (fields , rawTTs) = unzip construct
    exprs <- infer `mapM` rawTTs
    let (tts , tys) = unzip $ (\case { Core t ty -> (t , ty) }) <$> exprs
    pure $ Core (Cons (M.fromList $ zip fields tts)) [THProd (M.fromList $ zip fields tys)]

  P.Proj tt field -> do -- biunify (t+ <= {l:a})
    recordTy <- infer tt
    retTy <- _pSub . (V.! 0) . snd <$> withBiSubs 1 (\ix ->
      biSub_ (getArgTy recordTy)
             [THProd (M.singleton field [THVar ix])])
    pure $ case recordTy of
      Core f _ -> Core (Proj f field) retTy
      t -> t

  -- Sum
  -- TODO label should biunify with the label's type if known
  P.Label l tts -> do
    tts' <- infer `mapM` tts
    let unwrap = \case { Core t ty -> (t , ty) }
        (terms , tys) = unzip $ unwrap <$> tts'
    pure $ Core (Label l terms) [THSum $ M.fromList [(l , tys)]]

  P.Match alts -> let
      (labels , patterns , rawTTs) = unzip3 alts
    -- * find the type of the sum type being deconstructed
    -- * find the type of it's alts (~ lambda abstractions)
    -- * type of Match is (sumTy -> Join altTys)
    in do
    (exprs , vArgSubs) <-
      unzip <$> (withBiSubs 1 . (\t _->infer t)) `mapM` rawTTs
    let vArgTys = V.map _mSub <$> vArgSubs
        (altTTs , altTys) = unzip
          $ (\case { Core t ty -> (t , ty) }) <$> exprs
        argTys  = V.toList <$> vArgTys
        sumTy   = [THSum . M.fromList $ zip labels argTys]
        matchTy = [THArrow [sumTy] (concat $ altTys)]
        labelsMap = M.fromList $ zip labels altTTs
    pure $ Core (Match labelsMap Nothing) matchTy

  P.MultiIf branches -> do -- Bool ?
    let (rawConds , rawAlts) = unzip branches
        boolTy = getPrimIdx "Bool" & \case
          { Just i->THExt i; Nothing->error "panic: \"Bool\" not in scope" }
        addBool = doSub (-1) boolTy
    condExprs <- infer `mapM` rawConds
    alts      <- infer `mapM` rawAlts
    let retTy = foldr1 mergeTypes (getArgTy <$> alts) :: [TyHead]
        ifTy = [THArrow (addBool . getArgTy <$> condExprs) retTy]
        e2t (Core e ty) = e
    pure $ Core (MultiIf (zip (e2t<$>condExprs) (e2t<$>alts))) ifTy
    _

  P.TySum alts -> let
    mkTyHead mp = Ty $ [THSum mp]
    in do
      sumArgsMap <- (mapM infer) `mapM` M.fromList alts
      pure . mkTyHead $ map yoloGetTy <$> sumArgsMap

  --literals
  P.Lit l  -> pure $ Core (Lit l) [typeOfLit l]
  P.TyLit primTy -> pure $ Ty [THPrim primTy]

  -- desugar
  P.TyListOf t -> (\x-> Ty [THArray x]) . yoloGetTy <$> infer t
  P.InfixTrain lArg train -> infer $ resolveInfixes _ lArg train
  x -> error $ "not ready for tt: " ++ show x
