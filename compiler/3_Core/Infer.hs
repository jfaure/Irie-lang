-- see "Algebraic subtyping" by Stephen Dolan <https://www.cl.cam.ac.uk/~sd601/thesis.pdf>

module Infer where
import Prim
import BiUnify
import qualified ParseSyntax as P
import CoreSyn as C
import TCState
import PrettyCore
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

judgeModule :: P.Module -> Externs -> V.Vector Bind
judgeModule pm exts@(Externs extNames extBinds) = let
  nBinds = length $ pm ^. P.bindings
  nArgs  = pm ^. P.parseDetails . P.nArgs
  go  = judgeBind `mapM_` [0 .. nBinds-1]
  nFields = M.size (pm ^. P.parseDetails . P.fields)
  nLabels = M.size (pm ^. P.parseDetails . P.labels)
  in V.create $ do
    v       <- MV.new 0
    wips    <- MV.replicate nBinds WIP
    d       <- MV.new nArgs
    fieldsV <- MV.replicate nFields Nothing
    labelsV <- MV.replicate nLabels Nothing
    (\i->MV.write d i (BiSub [THArg i] [THArg i])) `mapM_` [0 .. nArgs-1]
    execStateT go $ TCEnvState
      { _pmodule  = pm
      , _externs  = exts
      , _wip      = wips
      , _bis      = v
      , _domain   = d
      , _fields   = fieldsV 
      , _labels   = labelsV
      }
    dv_ d
    pure wips

-- add argument holes to monotype env and guard against recursion
withDomain :: IName -> [Int] -> (TCEnv s a) -> TCEnv s (a , MV.MVector s BiSub)
withDomain bindINm idxs action = do
  d <- use domain
  -- anticipate recursive type
  use wip >>= (\v -> MV.write v bindINm (Checking [THRec bindINm]))
  r <- action
  argTys <- case idxs of
    [] -> MV.new 0
    x  -> pure $ MV.slice (head idxs) (length idxs) d
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
  b@BindOK{}  -> pure b
  Checking ty -> pure $ BindOK [] $ ULC (LCRec bindINm)
  WIP -> mdo
    P.FunBind hNm implicits matches tyAnn
      <- (!! bindINm) <$> use (id . pmodule . P.bindings)
    let (mainArgs , mainArgTys , tt) = matches2TT matches
--      args = implicits ++ mainArgs
        args = sort implicits -- TODO don't sort !
        nArgs = length args

    (expr , argSubs) <- withDomain bindINm args (infer tt)
    argTys <- fmap _mSub <$> V.freeze argSubs
    -- Generalization ?!
    let bindTy = case expr of
          Core x t -> if nArgs==0 then t else [THArrow (V.toList argTys) t]
          Ty t     -> if nArgs==0 then t else [THArrow (take nArgs (repeat [THSet 0])) t]
          ULC l    -> tyOfLC l
    case tyAnn of
      Nothing  -> pure ()
      Just ann -> do
        ann      <- tyExpr <$> infer ann
        argAnns  <- map tyExpr <$> (\[x]->infer x) `mapM` mainArgTys
--      let implicitArgTys = (\x->[THArg x]) `map` implicits
--          annTy = [THArrow implicitArgTys (tyExpr ann')]
        let annTy = case mainArgTys of
              [] -> ann
              x  -> [THArrow argAnns ann]
        exts <- use externs
        unless (check exts argTys bindTy annTy)
          $ error (show bindTy ++ "\n!<:\n" ++ show ann)
    let newBind = BindOK args expr
    (\v -> MV.write v bindINm newBind) =<< use wip
    pure newBind

infer :: P.TT -> TCEnv s Expr
infer = let
 yoloExpr2Ty :: Expr -> Type
 yoloExpr2Ty = \case
   Ty x -> x
   Core (Var v) typed -> case v of
     VBind i -> [THAlias i]
     VArg  i -> [THArg i]
     VExt  i -> [THExt i]
   ULC x -> [THULC x]
-- ULC x -> case x of
--   LCArg -> _
   x -> error $ "term found in type context: " ++ show x

  -- App is the only place things that can go wrong
  -- f x : biunify [Df n Dx]tx+ under (tf+ <= tx+ -> a)
  -- * ie. introduce result typevar 'a', and biunify (tf+ <= tx+ -> a)
 biUnifyApp fTy argTys = do
   bs <- snd <$> withBiSubs 1 (\idx -> biSub_ fTy [THArrow argTys [THVar idx]])
   _pSub <$> (`MV.read` 0) bs

   -- TODO verify argument subtypes for coercion purposes
 in \case
  P.WildCard -> pure $ Ty tyTOP
  -- vars : lookup in appropriate environment
  P.Var v -> case v of
    P.VBind b   -> -- polytype env
      judgeBind b <&> \case
        BindOK args (Ty ty) -> case args of
          []   -> Ty ty
          args -> Ty [THPi ((,[])<$>args) ty M.empty]
        BindOK args (Core e ty) -> Core (Var $ VBind b) ty
        BindOK args e -> e
        x -> error $ show x -- recursion guard ?
    P.VLocal l  -> do -- monotype env (fn args)
      pure $ ULC (LCArg l) -- pure $ Core (Var $ VArg l) [THArg l]
    P.VExtern i -> (`readParseExtern` i) <$> use externs

  P.App f' args' -> do
    f     <- infer f'
    args  <- infer `mapM` args'
    retTy <- biUnifyApp (tyOfExpr f) (tyOfExpr <$> args)
    pure $ case ttApp f args of
      Core f _ -> Core f retTy
      t -> t

  P.Cons construct -> do -- assign arg types to each label (cannot fail)
    let (fields , rawTTs) = unzip construct
    exprs <- infer `mapM` rawTTs
    let (tts , tys) = unzip $ (\case { Core t ty -> (t , ty) }) <$> exprs
    pure $ Core (Cons (M.fromList $ zip fields tts)) [THProd (M.fromList $ zip fields tys)]

  P.Proj tt field -> do -- biunify (t+ <= {l:a})
    recordTy <- infer tt
    bs <- snd <$> withBiSubs 1 (\ix ->
      biSub_ (tyOfExpr recordTy)
             [THProd (M.singleton field [THVar ix])])
    retTy <- _pSub <$> (`MV.read` 0) bs
    pure $ case recordTy of
      Core f _ -> Core (Proj f field) retTy
      t -> t

  -- Sum
  -- TODO label should biunify with the label's type if known
  P.Label l tts -> do
    tts' <- infer `mapM` tts
    ((`MV.read` l) =<< use labels) >>= \case
      Nothing -> error $ "forward reference to label unsupported: " ++ show l
      Just ty@[THArrow{}] -> do
        retTy <- biUnifyApp ty (tyOfExpr <$> tts')
        pure $ Core (Label l tts') retTy
      Just ty -> do
        pure $ Core (Label l tts') ty

  P.TySum alts -> do -- alts are function types
    -- 1. Check against ann (retTypes must all subsume the signature)
    -- 2. Create sigma type from the arguments
    -- 3. Create proof terms from the return types
    let go (l,impls,ty) = (l,) . mkSigma impls <$> infer ty
        mkSigma impls ty = let
          ty' = yoloExpr2Ty ty
          in case impls of
          [] -> ty'
          impls -> [THSi (map (,[]) impls) ty' M.empty]
    sumArgsMap <- go `mapM` alts
    labelsV <- use labels
    (\(l,t) -> MV.write labelsV l (Just t)) `mapM` sumArgsMap
--  pure $ Ty $ [THSum $ fst <$> sumArgsMap]
    pure $ Ty $ [THSum $ M.fromList sumArgsMap]

  P.Match alts -> let
      (labels , patterns , rawTTs) = unzip3 alts
    -- * find the type of the sum type being deconstructed
    -- * find the type of it's alts (~ lambda abstractions)
    -- * type of Match is (sumTy -> Join altTys)
      mkFn = \case { [] -> [THSet 0] ; x -> [THArrow (drop 1 x) [THSet 0]] }
      pattern2Ty = mkFn . \case
        [] -> []
        P.PArg _ : xs -> [THSet 0] : [pattern2Ty xs]
      tys = pattern2Ty <$> patterns
    in do
    altExprs <- infer `mapM` rawTTs
    let sumTy     = [THSum $ M.fromList (zip labels tys)] --(mergeTypes altTys)]
        retTy     = foldl mergeTypes [] $ yoloExpr2Ty <$> altExprs
        matchTy   = [THArrow [sumTy] retTy]
        labelsMap = M.fromList $ zip labels altExprs
    pure $ Core (Match labelsMap Nothing) matchTy

  P.MultiIf branches elseE -> do -- Bool ?
    let (rawConds , rawAlts) = unzip branches
        boolTy = getPrimIdx "Bool" & \case
          { Just i->THExt i; Nothing->error "panic: \"Bool\" not in scope" }
        addBool = doSub boolTy
    condExprs <- infer `mapM` rawConds
    alts      <- infer `mapM` rawAlts
    elseE'    <- infer elseE
    let retTy = foldr1 mergeTypes (tyOfExpr <$> (alts ++ [elseE'])) :: [TyHead]
        condTys = tyOfExpr <$> condExprs
        e2t (Core e ty) = e
        ifE = MultiIf (zip (e2t<$>condExprs) (e2t<$>alts)) (e2t elseE') 

    (`biSub_` [boolTy]) `mapM` condTys -- check the condTys all subtype bool
    pure $ Core ifE retTy

  -- desugar --
  P.LitArray literals -> let
    ty = typeOfLit (head literals) -- TODO merge (join) all tys ?
    in pure $ Core (Lit . Array $ literals) [THArray [ty]]

  P.Lit l  -> pure $ Core (Lit l) [typeOfLit l]
  P.TyListOf t -> (\x-> Ty [THArray x]) . yoloExpr2Ty <$> infer t
  P.InfixTrain lArg train -> infer $ resolveInfixes _ lArg train
  x -> error $ "inference engine not ready for parsed tt: " ++ show x

----------------
-- λ calculus --
----------------
lc2Ty = go' where
 go' x = [THULC x]
-- go = \case
--  LCArg i -> [THLamBound i]
-- LCApp lcf lca -> let
--   getArgs :: [LC] -> [LC]
--   getArgs (f:a) = case f of
--     LCApp f' a' -> getArgs [f',a'] ++ a
--     lc -> lc:a
--   (f : ars) = getArgs [lcf , lca]
--   in LCApp f argscase f of
--     LCArg i -> _
--     LCRec i -> [THRecApp i (ULC <$> ars)]
--     x -> error $ "LC not a function: " ++ show x
-- LCRec i   -> [THRecApp i []]
-- LCTerm t ty -> error $ "LC: expr is not a type: " ++ show t ++ " : " ++ show ty

lc2Term = \case
  LCArg i -> Var (VArg i)
  LCRec i -> Var (VBind i)
  LCApp a b   -> App (lc2Term a) [lc2Term b]
  LCTerm t ty -> t

onExprULC f = \case { ULC l -> f l ; x -> x }
expr2Term = onExprULC (\x->Core (lc2Term x) [])
expr2Ty =   onExprULC (Ty . lc2Ty)

tyOfLC = \case
  LCArg i -> [THArg i]
  LCApp a b -> [THArrow [tyOfLC a] (tyOfLC b)]
  LCRec a   -> [THRec a]
  LCTerm t ty -> ty

tyOfExpr  = \case
  Core x ty -> ty
  Ty t      -> [THSet 0]     -- type of types
  ULC l     -> tyOfLC l

solveULC f = \case
  ULC l -> f l
  x -> x
--  Set u t   -> [THSet (u+1)]

-----------------
-- TT Calculus --
-----------------
-- Application of typechecked TT expressions
-- This is different depending on the TT, one of:
-- * Untyped lambda-calculus
-- * Term app
-- * Type app: PI type and primitives (-> , %int n etc..)
ttApp :: Expr -> [Expr] -> Expr
ttApp fn args = case fn of
  ULC f      -> doULCApp  f
  Core f fTy -> doTermApp f fTy
  Ty t       -> doTypeApp t args
  where
  doULCApp f = let
    go = \case
      ULC b     -> ULC $ LCApp f b
      Core t ty -> ULC $ LCApp f (LCTerm t ty)
    in case args of
    [x] -> go x
    x:xs -> ttApp (go x) xs
  doTermApp f fTy = let
    (ars , end) = span (\case {Core{}->True ; _->False}) (expr2Term <$> args)
    app = App f $ (\(Core t _ty)->t) <$> ars 
    in case end of
      [] -> Core app [] -- don't forget to set retTy
      x  -> error $ "term applied to type: " ++ show app ++ show x
  doTypeApp t args = let ttArgs = expr2Ty <$> args in case t of
    f@[THPi ars ty typeArgs] -> case ars of
      (ar,arTy):arNms -> case (ty , ttArgs) of
          ([THInstr MkIntN ars] , [Core (Lit (Int i)) _]) -> Ty [THPrim (PrimInt $ fromIntegral i)]
          ([THInstr ArrowTy ars] , ttArgs) -> case solveULC (Ty . lc2Ty) <$> ttArgs of
              [Ty arg1 , Ty arg2] -> Ty [THArrow [arg1] arg2]
              x -> error $ "arguments to → must be types: " ++ show args
          _ -> let
            piApp expr = Ty [THPi arNms ty (M.insert ar expr typeArgs)]
            in case ttArgs of
              [expr]  -> piApp expr
              expr:xs -> ttApp (piApp expr) xs
      [] -> error $ "not a function: " ++ show f  ++ "\napplied to: " ++ show ttArgs
    f -> error $ "panic: not a function: " ++ show f ++ "\n applied to: " ++ show args
