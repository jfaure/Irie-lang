-- see "Algebraic subtyping" by Stephen Dolan <https://www.cl.cam.ac.uk/~sd601/thesis.pdf>

module Infer where
import Prim
import BiUnify
import qualified ParseSyntax as P
import CoreSyn as C
import CoreUtils
import TCState
import PrettyCore
import DesugarParse
import Externs

import Control.Lens
import Control.Monad
import Control.Monad.ST
import Control.Applicative
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Except
import Data.Functor
import Data.List
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV -- mutable vectors
import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS

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
      , _errors   = []
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

judgeBind :: IName -> TCEnv s Expr
judgeBind bindINm = use wip >>= (`MV.read` bindINm) >>= \case
  BindOK e  -> pure e
--Checking ty -> pure $ BindOK $ Ty [THRec bindINm]
  Checking ty -> pure $ Core (Var (VBind bindINm)) [THRec bindINm]
  WIP -> do
    P.FunBind hNm implicits freeVars matches tyAnn
      <- (!! bindINm) <$> use (pmodule . P.bindings)
    let (mainArgs , mainArgTys , tt) = matches2TT matches
        args = sort $ (map fst implicits) ++ mainArgs
--      args = sort implicits -- TODO don't sort !
        nArgs = length args

    (expr , argSubs) <- withDomain bindINm args (infer tt)
    argTys <- fmap _mSub <$> V.freeze argSubs
    -- Generalization ?!
    -- TODO argTys vs function Tys
    let inferredTy = case expr of
          Core x t -> t
--        CoreFn ars x t ->
          Ty t     -> t
--      mkArrow t = if nArgs==0 then t else [THArrow (V.toList argTys) t]
    bindTy <- case tyAnn of
      Nothing  -> pure inferredTy
      Just ann -> do
        ann <- tyExpr <$> infer ann
        let inferArg = \case { [x] -> tyExpr <$> infer x ; [] -> pure [THSet 0] }
        argAnns  <- inferArg `mapM` mainArgTys
        let annTy = case mainArgTys of { [] -> ann ; x  -> [THArrow argAnns ann] }
        exts <- use externs
        labelsV <- V.freeze =<< use labels
        unless (check exts argTys labelsV inferredTy annTy)
          $ error (show inferredTy ++ "\n!<:\n" ++ show ann)
        -- Prefer user's type annotation over the inferred one; except
        -- TODO we may have inferred some missing information !
        -- type families are special: we need to insert the list of labels as retTy
        pure $ case getRetTy inferredTy of
          s@[THFam{}] -> case flattenArrowTy annTy of
            [THArrow d r] -> [THFam r d []]
            x -> s
          _ -> annTy
    let newExpr = case args of
          [] -> expr
          args -> case expr of
            Core x ty -> CoreFn (zip args (V.toList argTys)) IS.empty x bindTy
--          Ty t      -> d_ bindTy $ Ty $ [THPi $ Pi (zip args $ V.toList argTys) t]
            Ty t      -> Ty $ bindTy
    (\v -> MV.write v bindINm (BindOK newExpr)) =<< use wip
    pure expr

infer :: P.TT -> TCEnv s Expr
infer = let
  -- App is the only place things that can go wrong
  -- f x : biunify [Df n Dx]tx+ under (tf+ <= tx+ -> a)
  -- * ie. introduce result typevar 'a', and biunify (tf+ <= tx+ -> a)
 biUnifyApp fTy argTys = do
   bs <- snd <$> withBiSubs 1 (\idx -> biSub_ fTy [THArrow argTys [THVar idx]])
   _pSub <$> (`MV.read` 0) bs

   -- TODO verify argument subtypes for coercion purposes
 in \case
  P.WildCard -> pure $ Core Hole [THSet 0]
  -- vars : lookup in appropriate environment
  P.Var v -> case v of
    P.VBind b   -> -- polytype env
      judgeBind b <&> \case
        CoreFn args free e ty -> let
          mkArrow args t = case args of { []->t ; args->[THArrow (snd <$> args) t] }
          in Core (Var $ VBind b) (mkArrow args ty)
        Core e ty -> Core (Var $ VBind b) ty -- don't copy the body
        t -> t
    P.VLocal l  -> do -- monotype env (fn args)
      pure $ Core (Var $ VArg l) [THArg l]
    P.VExtern i -> (`readParseExtern` i) <$> use externs

  P.App f' args' -> do
    f     <- infer f'
    args  <- infer `mapM` args'
    retTy <- biUnifyApp (tyOfExpr f) (tyOfExpr <$> args)
    ttApp judgeBind f args <&> \case
      Core f _ -> Core f retTy
      t -> t

  P.Cons construct -> do -- assign arg types to each label (cannot fail)
    let (fields , rawTTs) = unzip construct
    exprs <- infer `mapM` rawTTs
    let (tts , tys) = unzip $ (\case { Core t ty -> (t , ty) }) <$> exprs
    pure $ Core (Cons (IM.fromList $ zip fields tts)) [THProd fields]

  P.Proj tt field -> do -- biunify (t+ <= {l:a})
    recordTy <- infer tt
    bs <- snd <$> withBiSubs 1 (\ix ->
      biSub_ (tyOfExpr recordTy) [THProd [field]]) --  M.singleton field [THVar ix])])
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
      Just ty -> if isArrowTy ty
        then do
          retTy <- biUnifyApp ty (tyOfExpr <$> tts')
          pure $ Core (Label l tts') retTy
        else pure $ Core (Label l tts') ty

  P.TySum alts -> do -- alts are function types
    -- 1. Check against ann (retTypes must all subsume the signature)
    -- 2. Create sigma type from the arguments
    -- 3. Create proof terms from the return types
    let go (l,impls,ty) = (l,) <$> (mkSigma (map fst impls) =<< infer ty)
        mkSigma impls ty = do
          ty' <- expr2Ty judgeBind ty
          pure $ case impls of
            [] -> ty'
            impls -> [THPi $ Pi (map (,[THSet 0]) impls) ty']
    sumArgsMap <- go `mapM` alts
    labelsV <- use labels
    (\(l,t) -> MV.write labelsV l (Just t)) `mapM` sumArgsMap
    let sumTy = [THSum $ fst <$> sumArgsMap]
        returnTypes = getFamilyTy . snd <$> sumArgsMap
        getFamilyTy x = case getRetTy x of -- TODO currying ?
--        [THRecSi m ars] -> [THArrow (take (length ars) $ repeat [THSet 0]) sumTy]
          [THRecSi m ars] -> [THFam sumTy (take (length ars) $ repeat [THSet 0]) []]
          x -> sumTy
        dataTy = foldl1 mergeTypes $ returnTypes
    pure $ Ty dataTy

  P.Match alts -> let
      (altLabels , freeVars , patterns , rawTTs) = unzip4 alts
    -- * find the type of the sum type being deconstructed
    -- * find the type of it's alts (~ lambda abstractions)
    -- * type of Match is (sumTy -> Join altTys)
      mkFnTy = \case { [] -> [THSet 0] ; x -> [THArrow (drop 1 x) [THSet 0]] }
      pattern2Ty = mkFnTy . \case
        [] -> []
        P.PArg _ : xs -> [THSet 0] : [pattern2Ty xs]
      tys = pattern2Ty <$> patterns
    in do
    d_ freeVars $ pure ()
    altExprs <- infer `mapM` rawTTs
    --TODO merge types with labels (mergeTypes altTys)]
    retTy <- foldl mergeTypes [] <$> pure (tyOfExpr <$> altExprs)
    let scrutTy = [THSplit altLabels]
        matchTy = [THArrow [scrutTy] retTy]
        unpat = \case { P.PArg i -> i ; x -> error $ "not ready for patter: " ++ show x }
        mkFn pat free (Core t ty) = CoreFn ((,[]) . unpat <$> pat) free t ty
        alts    = zipWith3 mkFn patterns freeVars altExprs
        altLabelsMap = IM.fromList $ zip altLabels alts
    pure $ Core (Match altLabelsMap Nothing) matchTy

--P.MultiIf branches elseE -> do -- Bool ?
--  let (rawConds , rawAlts) = unzip branches
--      boolTy = getPrimIdx "Bool" & \case
--        { Just i->THULC (LCRec i); Nothing->error "panic: \"Bool\" not in scope" }
--      addBool = doSub boolTy
--  condExprs <- infer `mapM` rawConds
--  alts      <- infer `mapM` rawAlts
--  elseE'    <- infer elseE
--  let retTy = foldr1 mergeTypes (tyOfExpr <$> (alts ++ [elseE'])) :: [TyHead]
--      condTys = tyOfExpr <$> condExprs
--      e2t (Core e ty) = e
--      ifE = MultiIf (zip (e2t<$>condExprs) (e2t<$>alts)) (e2t elseE') 

--  (`biSub_` [boolTy]) `mapM` condTys -- check the condTys all subtype bool
--  pure $ Core ifE retTy

  -- desugar --
  P.LitArray literals -> let
    ty = typeOfLit (head literals) -- TODO merge (join) all tys ?
    in pure $ Core (Lit . Array $ literals) [THArray [ty]]

  P.Lit l  -> pure $ Core (Lit l) [typeOfLit l]
--  P.TyListOf t -> (\x-> Ty [THArray x]) . yoloExpr2Ty <$> infer t
  P.InfixTrain lArg train -> infer $ resolveInfixes (\_->const True) lArg train -- TODO
  x -> error $ "inference engine not ready for parsed tt: " ++ show x

-----------------
-- TT Calculus --
-----------------
-- How to handle Application of mixtures of types and terms
--ttApp :: _ -> Expr -> [Expr] -> TCEnv s Expr
ttApp readBind fn args = -- trace (clYellow (show fn ++ " $ " ++ show args)) $
 case fn of
  Core cf ty -> case cf of
    Instr (TyInstr Arrow)  -> expr2Ty readBind `mapM` args <&> \case
      { [a , b] -> Ty [THArrow [a] b] }
    Instr (TyInstr MkIntN) -> case args of
      [Core (Lit (Int i)) ty] -> pure $ Ty [THPrim (PrimInt $ fromIntegral i)]
    coreFn -> let
      (ars , end) = span (\case {Core{}->True ; _->False}) args
      app = App cf $ (\(Core t _ty)->t) <$> ars -- drop argument types
      in pure $ case end of
        [] -> Core app [] -- don't forget to set retTy
        x  -> error $ "term applied to type: " ++ show app ++ show x
  Ty f -> case f of -- always a type family
    -- TODO match arities ?
    [THFam f a ixs] -> pure $ Ty [THFam f (drop (length args) a) (ixs ++ args)]
--  x -> pure $ Ty [THFam f [] args]
    x -> error $ "ttapp panic: " ++ show x ++ " $ " ++ show args
  _ -> error $ "ttapp: not a function: " ++ show fn ++ " $ " ++ show args
