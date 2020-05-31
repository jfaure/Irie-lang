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
--import qualified Data.Vector.Generic.Mutable as MV (growFront) -- mutable vectors
import Control.Monad.ST
import qualified Data.Map as M
import qualified Data.IntMap as IM
import qualified Data.Text as T
import Data.Functor
import Control.Monad
import Control.Applicative
import Control.Monad.Trans.State.Strict
import Data.List --(foldl', intersect)
import Data.STRef
import Control.Lens

import Debug.Trace

-- test1 x = x.foo.bar{foo=3}

judgeModule :: P.Module -> Externs -> V.Vector Bind
judgeModule pm exts@(Externs extNames extBinds) = let
  nBinds = length $ pm ^. P.bindings
  go  = judgeBind `mapM_` [0 .. nBinds-1]
  in V.create $ do
    v    <- MV.new 0
    wips <- MV.replicate nBinds WIP
    d    <- MV.new 0
    execStateT go $ TCEnvState
      { _pmodule  = pm
      , _externs  = exts
      , _wip      = wips
      , _bis      = v
      , _domain   = d
      }
    pure wips

-- add argument holes to monotype env and guard potential recursion
withDomain :: IName -> Int -> (TCEnv s a) -> TCEnv s (a , MV.MVector s BiSub)
withDomain bindINm n action = do
  oldD <- use domain
  d <- MV.grow oldD n
  let l = MV.length d
      idxs = [l-n .. l-1]
      tvars = (\x->[THVar x]) <$> idxs
  (\i->MV.write d i (BiSub [THArg i] [THArg i])) `mapM` idxs
--(\i->MV.write d i (BiSub [] [])) `mapM` idxs
  -- anticipate recursive type
  use wip >>= (\v -> MV.write v bindINm
    $ Checking [THArrow tvars [THRec bindINm]])
  domain .= d
  r <- action
  argTys <- MV.slice (l-n) n <$> use domain
--  domain %= MV.slice 0 (l-n)
  pure (r , argTys)

-- do a bisub with typevars
withBiSubs :: Int -> (Int->TCEnv s a) -> TCEnv s (a , MV.MVector s BiSub)
withBiSubs n action = do
  bisubs <- use bis
  let biSubLen = MV.length bisubs
      genFn i = let tv = [THVar i] in BiSub tv tv
  bisubs <- MV.grow bisubs n
  (\i->MV.write bisubs i (genFn i)) `mapM` [biSubLen .. biSubLen+n-1]
  bis .= bisubs
  ret <- action biSubLen
  let vars = MV.slice biSubLen n bisubs
  pure (ret , vars)

judgeBind :: IName -> TCEnv s Bind
judgeBind bindINm = use wip >>= (`MV.read` bindINm) >>= \case
  t@BindTerm{} -> pure t
  t@BindType{} -> pure t
  Checking  ty -> pure $ BindTerm [] (Var$VBind bindINm) ty
  WIP -> mdo
    P.FunBind hNm implicits matches tyAnn
      <- (!! bindINm) <$> use (id . pmodule . P.bindings)
    let (mainArgs , mainArgTys , tt) = matches2TT matches
        args = implicits ++ mainArgs
        nArgs = length args

    (expr , argSubs) <- withDomain bindINm nArgs (infer tt)
--  traceShowM =<< V.freeze argSubs
--  traceShowM =<< (V.freeze =<< use bis)
    argTys <- fmap _mSub <$> V.freeze argSubs
    -- Generalization ?!
    (newBind , bindTy) <- case expr of
      Core x t -> let
        bindTy=if nArgs==0 then t else[THArrow (V.toList argTys) t]
        in pure $ (BindTerm args x bindTy , bindTy)
      Ty   t   -> pure $ (BindType args t , [THSet 0]) -- args ? TODO
    case tyAnn of
      Nothing  -> pure ()
      Just ann -> do
        ann' <- infer ann
        let implicitArgTys = (\x->[THArg x]) `map` implicits
            annTy = [THArrow implicitArgTys (tyExpr ann')]
        exts <- use externs
        unless (check exts argTys bindTy annTy)
          $ error (show bindTy ++ "\n!<:\n" ++ show ann')
    (\v -> MV.write v bindINm newBind) =<< use wip
    pure newBind

infer :: P.TT -> TCEnv s Expr
infer = let
 -- expr found in type context (should be a type or var)
 -- in product types, we fold with ttApp to find type arguments
 yoloGetTy :: Expr -> Type
 yoloGetTy = \case
   Ty x -> x
   Core (Var v) typed -> case v of
     VBind i -> [THAlias i]
     VArg  i -> [THArg i]
     VExt  i -> [THExt i]
   Core e ty -> _ --[THEta e ty]
   x -> error $ "type expected: " ++ show x
 in \case
  P.WildCard -> _
  -- vars : lookup in appropriate environment
  P.Var v -> case v of
    P.VBind b   ->    -- polytype env
     -- guard recursion
      judgeBind b <&> \case
        BindTerm args e ty -> Core (Var $ VBind b) ty
        BindType args ty -> Ty ty
        x -> error $ show x
    P.VLocal l  -> do -- monotype env (fn args)
      pure $ Core (Var $ VArg l) [THArg l]
    P.VExtern i -> do
--    extIdx <- (V.! i) <$> use noScopes
--    (V.! extIdx) <$> use externs
      (`readParseExtern` i) <$> use externs
    x -> error $ show x

  -- APP: f : [Df-]ft+ , Pi ^x : [Df-]ft+ ==> e2:[Dx-]tx+
  -- |- f x : biunify [Df n Dx]tx+ under (tf+ <= tx+ -> a)
  -- * introduce a typevar 'a', and biunify (tf+ <= tx+ -> a)
  -- Dependent App:
  -- Structurally infer dependents:
  -- * dependent function space: only for typechecking purposes
  -- * Building sigma
  -- * extracting sigma
  P.App f args -> let
--  ttApp :: Expr -> Expr -> Expr
--  ttApp a b = case (a , b) of
--    (Core t ty , Core t2 ty2) -> case t of
--      App f x -> Core (App f (x++[t2])) [] -- dont' forget to set retTy
--      _       -> Core (App t [t2])      []
--    (Ty s , Ty s2)         -> Ty$ [THIxType s s2]       -- type index
--    (Ty s , c@(Core t ty)) -> Ty$ [THIxTerm s (t , ty)] -- term index
--    (c@(Core t ty) , Ty s) -> Ty$ [THEta t s] -- only valid if c is an eta expansion
    ttApp :: Expr -> Expr -> Expr
    ttApp a b = case (a , b) of
      (Core t ty , Core t2 ty2) -> case t of
        App f x -> Core (App f (x++[t2])) [] -- dont' forget to set retTy
        _       -> Core (App t [t2])      []
      (Ty s , depArg) -> case s of 
        [THIx t deps] -> Ty [THIx t (deps ++ [depArg])]
        t             -> Ty [THIx t [depArg]]
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
        bs <- snd <$> withBiSubs 1 (\idx ->
            biSub_ (getArgTy f') [THArrow (getArgTy <$> args') [THVar idx]])
        retTy <- _pSub <$> (`MV.read` 0) bs
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
    bs <- snd <$> withBiSubs 1 (\ix ->
      biSub_ (getArgTy recordTy)
             [THProd (M.singleton field [THVar ix])])
    retTy <- _pSub <$> (`MV.read` 0) bs
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

--P.Match alts -> let
--    (labels , patterns , rawTTs) = unzip3 alts
--  -- * find the type of the sum type being deconstructed
--  -- * find the type of it's alts (~ lambda abstractions)
--  -- * type of Match is (sumTy -> Join altTys)
--  in do
--  (exprs , vArgSubs) <-
--    unzip <$> (withBiSubs 1 . (\t _->infer t)) `mapM` rawTTs
--  let vArgTys = (_mSub <$>) <$> vArgSubs
--      (altTTs , altTys) = unzip
--        $ (\case { Core t ty -> (t , ty) }) <$> exprs
--      argTys  = V.toList <$> vArgTys
--      sumTy   = [THSum . M.fromList $ zip labels argTys]
--      matchTy = [THArrow [sumTy] (concat $ altTys)]
--      labelsMap = M.fromList $ zip labels altTTs
--  pure $ Core (Match labelsMap Nothing) matchTy

  P.MultiIf branches elseE -> do -- Bool ?
    let (rawConds , rawAlts) = unzip branches
        boolTy = getPrimIdx "Bool" & \case
          { Just i->THExt i; Nothing->error "panic: \"Bool\" not in scope" }
        addBool = doSub boolTy
    condExprs <- infer `mapM` rawConds
    alts      <- infer `mapM` rawAlts
    elseE'    <- infer elseE
    let retTy = foldr1 mergeTypes (getArgTy <$> (alts ++ [elseE'])) :: [TyHead]
        condTys = getArgTy <$> condExprs
        e2t (Core e ty) = e
        ifE = MultiIf (zip (e2t<$>condExprs) (e2t<$>alts)) (e2t elseE') 

    (`biSub_` [boolTy]) `mapM` condTys -- check the condTys all subtype bool
--  dv_ =<< use bis
    pure $ Core ifE retTy

  P.TySum alts -> let
    mkTyHead mp = Ty $ [THSum mp]
    in do
      sumArgsMap <- (mapM infer) `mapM` M.fromList alts
      pure . mkTyHead $ map yoloGetTy <$> sumArgsMap

  -- desugar
  P.Lit l  -> pure $ Core (Lit l) [typeOfLit l]
  P.TyListOf t -> (\x-> Ty [THArray x]) . yoloGetTy <$> infer t
  P.InfixTrain lArg train -> infer $ resolveInfixes _ lArg train
  x -> error $ "not ready for tt: " ++ show x
