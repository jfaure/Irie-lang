-- see "Algebraic subtyping" by Stephen Dolan https://www.cl.cam.ac.uk/~sd601/thesis.pdf
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
import Data.List (unzip4, zipWith4, foldl1, span)
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.Map as M
import qualified Data.IntMap as IM

judgeModule :: P.Module -> V.Vector HName -> Externs -> JudgedModule
judgeModule pm hNames exts = let
  nBinds  = length $ pm ^. P.bindings
  nArgs   = pm ^. P.parseDetails . P.nArgs
  nFields = M.size (pm ^. P.parseDetails . P.fields)
  nLabels = M.size (pm ^. P.parseDetails . P.labels)
  pBinds' = V.fromListN nBinds (pm ^. P.bindings)
  in runST $ do
    bis'      <- MV.new 0
    deBruijn' <- MV.new 0
    wip'      <- MV.replicate nBinds WIP
    domain'   <- MV.new nArgs
    qtt'      <- MV.replicate nArgs (QTT 0 0)
    fieldsV   <- MV.replicate nFields Nothing
    labelsV   <- MV.replicate nLabels Nothing
    [0 .. nArgs-1] `forM_` \i -> MV.write domain' i (BiSub [] []) --(BiSub [THArg i] [THArg i])

    st <- execStateT (judgeBind `mapM_` [0 .. nBinds-1]) $ TCEnvState
      { -- _pmodule  = pm
        _pBinds   = pBinds'
      , _bindWIP  = 0
      , _externs  = exts
      , _wip      = wip'
      , _mode     = Reader
      , _bis      = bis'
      , _deBruijn = deBruijn'
      , _level    = Dominion (-1,-1)
      , _quants   = 0
      , _domain   = domain'
      , _qtt      = qtt'
      , _fields   = fieldsV
      , _labels   = labelsV
      , _errors   = []
      }

    bis''    <- V.unsafeFreeze (st ^. bis)
    domain'' <- V.unsafeFreeze (st ^. domain)
    wip''    <- V.unsafeFreeze (st ^. wip)
    qtt''    <- V.unsafeFreeze (st ^. qtt)
    pure $ JudgedModule hNames wip'' bis'' qtt'' domain''

-- generalisation (and therefore type checking of usertypes) happens here
judgeBind :: IName -> TCEnv s Expr
judgeBind bindINm = use wip >>= \wip' -> (wip' `MV.read` bindINm) >>= \case
  BindOK e                  -> pure e

  Guard mutuals ars -> do
    this <- use bindWIP
    when (this /= bindINm) $ do
      MV.write wip' bindINm (Guard (this:mutuals) ars)
      MV.modify wip' (\(Guard ms ars) -> Guard (bindINm:ms) ars) this
    pure $ Core (Var (VBind bindINm)) [THRec bindINm]

  Mutual d e -> pure e

  WIP -> use wip >>= \wip' -> do
    svwip <- bindWIP <<.= bindINm

    let getTT (P.FunBind hNm implicits freeVars matches tyAnn) = let
          (mainArgs , mainArgTys , tt) = matches2TT matches
          args = sort $ (map fst implicits) ++ mainArgs -- TODO don't sort !
          in (tt , args)

    (tt , args) <- getTT . (V.! bindINm) <$> use pBinds
    traceShowM args -- TODO args should always be consecutive !!
    MV.write wip' bindINm (Guard [] args)

    svLvl <- use level
    level .= Dominion (snd (tVarRange svLvl) + 1, snd (tVarRange svLvl))
    expr <- infer tt
    let jb = case expr of
          Core x ty -> case args of
            [] -> Core x ty
            ars-> Core (Abs (zip ars ((\x->[THArg x]) <$> args)) mempty x ty) ty
          t -> t

    bindWIP .= svwip

    Guard ms _ars <- MV.read wip' bindINm
    cd <- use level
    MV.write wip' bindINm (Mutual cd jb)
    if (minimum (bindINm:ms) == bindINm) then fromJust . head <$> generaliseBinds bindINm ms else pure jb
-- Check annotation if given (against non-generalised type ??)
--bindTy <- maybe (pure genTy) (\ann -> checkAnnotation ann genTy mainArgTys (V.fromList argTys)) tyAnn

generaliseBinds i ms = use wip >>= \wip' -> do
  let getArs = \case { Core (Abs ars free x ty) t -> (fst <$> ars) ; _->[] }
  let genMutual m = do
        Mutual cd naiveExpr <- MV.read wip' m
        let args = getArs naiveExpr
        q <- gen args cd
        pure (m,q,args,cd,naiveExpr)
  let substVars = \(m,q,args,cd,naiveExpr) -> do
        done <- case naiveExpr of
          Core (Abs ars free x _ty) ty -> do
            (arTys , g) <- substTVars q args cd ty
            pure $ Core (Abs ars free x g) g
          t -> pure t
        MV.write wip' m $ BindOK done
        pure done
  things <- (i : ms) `forM` genMutual
  things `forM` substVars
 
checkAnnotation :: P.TT -> Type -> [[P.TT]] -> V.Vector Type -> TCEnv s Type
checkAnnotation ann inferredTy mainArgTys argTys = do
  ann <- tyExpr <$> infer ann
  let inferArg = \case { [x] -> tyExpr <$> infer x ; [] -> pure [THSet 0] }
  argAnns  <- inferArg `mapM` mainArgTys
  let annTy = case mainArgTys of { [] -> ann ; x  -> [THArrow argAnns ann] }
  exts <- use externs
  labelsV <- V.freeze =<< use labels
  unless (check exts argTys labelsV inferredTy annTy)
    $ error (show inferredTy <> "\n!<:\n" <> show ann)
  -- ? Prefer user's type annotation over the inferred one; except
  -- TODO we may have inferred some missing information !
  -- type families are special: we need to insert the list of labels as retTy
  pure $ case getRetTy inferredTy of
    s@[THFam{}] -> case flattenArrowTy annTy of
      [THArrow d r] -> [THFam r d []]
      x -> s
    _ -> annTy

-- TODO have to rename debruijn bound variables
gen ars dom = do
  quants .= 0
  let rmTVar n   = filter $ \case { THVar x -> x /= n ; _ -> True }
      rmArgVar n = filter $ \case { THArg x -> x /= n ; _ -> True }
      incQuant = quants <<%= (+1) :: TCEnv s Int
      -- have to recurse through the tvar types: remove stale debruijn refs and simplify the types
      generaliseBisubs range b = range `forM` \i -> MV.read b i >>= \s -> case trace (show i <> ": " <> show s :: Text) s of
        BiSub p m -> MV.write b i (BiSub (rmArgVar i $ rmTVar i p) (rmArgVar i $ rmTVar i m))
  let Dominion (bStart , bEnd) = dom
  traceM $ "gen: " <> show ars <> " , " <> show dom
  use bis    >>= \b -> generaliseBisubs [bStart .. bEnd] b
  use domain >>= generaliseBisubs ars
  quants <<.= 0

substTVars q'''''' ars dom inferredTy = let
  -- recursively substitute type vars
  argTys = (\x->[THArg x]) <$> ars
  subst pos ty = foldr mergeTypes [] <$> mapM (substTyHead pos) ty
  substTyHead pos ty = let
    incQuants = quants <<%= (+1)
    subst' = subst pos
    getTy = if pos then _pSub else _mSub
    in case ty of
-- TODO only over appropriate sub ?
-- TODO what exactly to generalise ?
-- [] -> (quants <<%= +1)) >>= \q -> MV.modify b (\(BiSub a b) -> BiSub (THBound q : a) (THBound q:b)) v $> [THBound q]
    THVar v -> use bis >>= \b -> (MV.read b v >>= subst' . getTy) >>= \case
      [] -> do incQuants >>= \q -> MV.write b v (BiSub [THBound q] [THBound q]) $> [THBound q]
      x  -> pure x

    THArg v -> use domain >>= \d -> (MV.read d v >>= subst' . getTy) >>= \case
      [] -> incQuants >>= \q -> MV.write d v (BiSub [THBound q] [THBound q]) $> [THBound q] --pure [THBound 0]
      x  -> pure x

    THArrow ars ret -> (\arsTy retTy -> [THArrow arsTy retTy]) <$> subst (not pos) `mapM` ars <*> subst' ret
    THProduct tys -> (\x->[THProduct x]) <$> (subst' `traverse` tys)
    THBi b ty -> (\t->[THBi b t]) <$> subst' ty

    -- TODO is a bit weird , need to review handling of recursive types when inferring mutual functions
    THRec r   -> use wip >>= \wip' -> getRetTy . tyOfExpr . (\(BindOK b) -> b) <$> MV.read wip' r
    t -> pure [t]
  in do
  rawGenTy <- subst True (addArrowArgs argTys inferredTy)
  q <- use quants
  traceM $ toS $ "Subst: " <> show q <> ". " <> prettyTyRaw (addArrowArgs argTys inferredTy)
  let genTy = if q > 0 then [THBi q rawGenTy] else rawGenTy
  traceM (toS $ prettyTyRaw genTy)
  pure (argTys , genTy)

infer :: P.TT -> TCEnv s Expr
infer = let
  -- App is the only place typechecking can fail
  -- f x : biunify [Df n Dx]tx+ under (tf+ <= tx+ -> a)
 biUnifyApp fTy argTys = do
   (biret , [oneTy]) <- withBiSubs 1 (\idx -> biSub_ fTy (addArrowArgs argTys [THVar idx]))
   pure (biret , [THVar oneTy])

 in \case
  P.WildCard -> pure $ Core Hole [THSet 0]

  P.Var v -> let
      judgeLocalBind b = judgeBind b <&> \case
        Core e ty -> Core (Var $ VBind b) ty -- don't copy the body
        t -> t
    in case v of -- vars : lookup in appropriate environment
    P.VBind b   -> judgeLocalBind b -- polytype env
    P.VLocal l  -> do -- monotype env (fn args)
      use qtt >>= \qttV -> use mode >>= \case
        Reader  -> MV.modify qttV (over qttReads (+1)) l
        Builder -> MV.modify qttV (over qttBuilds (+1)) l
      pure $ Core (Var $ VArg l) [THArg l]
    P.VExtern i -> (`readParseExtern` i) <$> use externs >>= \case
      Left b  -> judgeLocalBind b -- was a forward reference not an extern
      Right e -> pure e

  P.Abs top -> let
    -- unlike topBind, don't bother generalising the type
      getTT (P.FunBind hNm implicits freeVars matches tyAnn) = let
        (mainArgs , mainArgTys , tt) = matches2TT matches
        args = sort $ (map fst implicits) ++ mainArgs -- TODO don't sort !
        in (tt , args)
      (tt , args) = getTT top
    in do
    traceShowM args -- TODO args should always be consecutive !!
    infer tt <&> \case
      Core x ty -> case args of
        [] -> Core x ty
        ars-> let
          argTys = (\x->[THArg x]) <$> ars
          ty'    = addArrowArgs argTys ty
          in Core (Abs (zip ars ((\x->[THArg x]) <$> args)) mempty x ty') ty'
      t -> t

  P.App fTT argsTT -> do
    f    <- infer fTT
    args <- tcStateLocalMode $ use qtt >>= \qtts -> do
      -- Note. not all fn sig args are explicit (esp. primInstrs), which is problematic for QTT
      -- So I pad missing modes with Reader, but this is slightly suspicious
        argModes <- (\case { Core (Abs ars _ _ _) _ -> ars ; _ -> [] }) f `forM` \(i,_ty) ->
          MV.read qtts i <&> \(QTT _reads builds) -> if builds > 0 then Builder else Reader
        zipWithM (\m argExpr -> (mode .= m) *> infer argExpr) (argModes ++ repeat Reader) argsTT
    (biret , retTy) <- biUnifyApp (tyOfExpr f) (tyOfExpr <$> args)
    let castArg (a :: Term) = \case { BiCast f -> App f [a] ; _ -> a }
        castArgs args' cast = case cast of
          CastApp ac maybePap -> zipWith castArg args' (ac ++ repeat BiEQ) -- TODO why not enough bisubs ?!
          x -> args'
    x <- ttApp judgeBind f args <&> \case -- ! we must set the retTy since ttApp doesn't
      Core (App f args) _ -> case biret of
        CastApp _ (Just pap) -> let -- handle PAp
          mkpap = Instr (MkPAp (length pap))
          in Core (App mkpap (f : castArgs args biret)) retTy
        CastApp _ Nothing    -> Core (App f (castArgs args biret)) retTy
        _ -> Core (App f args) retTy --error $ show x
      Core f _ -> Core f retTy
      t -> t
    pure x

  P.Cons construct -> do
    let (fields , rawTTs) = unzip construct
    exprs <- infer `mapM` rawTTs
    let (tts , tys) = unzip $ (\case { Core t ty -> (t , ty) }) <$> exprs
    pure $ Core (Cons (IM.fromList $ zip fields tts)) [THProduct (IM.fromList $ zip fields tys)]

  P.TTLens tt fields maybeSet -> let
    in do
    record <- infer tt
    let recordTy = tyOfExpr record
        mkExpected :: Type -> Type
        mkExpected dest = foldr (\fName ty -> [THProduct (IM.singleton fName ty)]) dest fields
    case record of
      Core f _ -> case maybeSet of
        -- for get, we need a typevar for the destination
        P.LensGet    -> do
          (_bs , [retTy]) <- withBiSubs 1 $ \ix -> biSub recordTy (mkExpected [THVar ix])
--        retTy <- _pSub <$> (`MV.read` 0) (snd bs)
          pure $ Core (TTLens f fields LensGet) [THVar retTy]
        -- for others, use the type of the ammo
        P.LensSet x  -> infer x >>= \ammo -> let expect = mkExpected (tyOfExpr ammo)
          in biSub recordTy expect $> Core (TTLens f fields (LensSet ammo)) expect
        P.LensOver x -> infer x >>= \fn -> do
          (bs , [retTy]) <- withBiSubs 1 $ \ ix -> biSub recordTy (mkExpected [THVar ix])
--        retTy <- _pSub <$> (`MV.read` 0) (snd bs)
--        biSub (tyOfExpr fn) [THBi 1 [THArrow [retTy] [THBound 0]]]
          pure $ Core (TTLens f fields (LensOver fn)) [THVar retTy]
      t -> panic "record type must be a term" -- pure t

  -- Sum
  -- TODO recursion + qtt is problematic
  P.Label l tts -> do
    tts' <- tcStateLocalMode $ do { mode .= Builder ; infer `mapM` tts }
    ((`MV.read` l) =<< use labels) >>= \case
      Nothing -> error $ "forward reference to label unsupported: " <> show l
      Just ty -> if isArrowTy ty
        then do
          (biret , retTy) <- biUnifyApp ty (tyOfExpr <$> tts')
          pure $ Core (Label l tts') retTy
        else pure $ Core (Label l tts') ty

--P.Label l tts -> infer `mapM` tts <&> \exprs ->
--  Core (Label l exprs) [THSumty $ IM.singleton l (tyOfExpr <$> exprs)]

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
    altExprs <- infer `mapM` rawTTs
    let unJust = \case { Just x -> x ; Nothing -> error "need labelType" }
    labTys   <- map unJust <$> (use labels >>= \l -> (MV.read l) `mapM` altLabels)
    let getArgTys = \case
          [THArrow ars1 r] -> ars1 ++ getArgTys r-- TODO more nesting ?
          t -> [t]
        argTys = getArgTys <$> labTys
    --TODO merge types with labels (mergeTypes altTys)]
    retTy <- foldl mergeTypes [] <$> pure (tyOfExpr <$> altExprs)
    let scrutTy = [THSplit altLabels]
        matchTy = [THArrow [scrutTy] retTy]
        unpat = \case { P.PArg i -> i ; x -> error $ "not ready for pattern: " <> show x }
        mkFn argTys pat free (Core t ty) = Core (Abs (zip (unpat <$> pat) argTys) free t ty) ty
        alts    = zipWith4 mkFn argTys patterns freeVars altExprs
        altLabelsMap = IM.fromList $ zip altLabels alts
    pure $ Core (Match retTy altLabelsMap Nothing) matchTy

  -- desugar --
  P.LitArray literals -> let
    ty = typeOfLit (fromJust $ head literals) -- TODO merge (join) all tys ?
    in pure $ Core (Lit . Array $ literals) [THArray [ty]]

  P.Lit l  -> pure $ Core (Lit l) [typeOfLit l]
--  P.TyListOf t -> (\x-> Ty [THArray x]) . yoloExpr2Ty <$> infer t
  P.InfixTrain lArg train -> infer $ resolveInfixes (\_->const True) lArg train -- TODO
  x -> error $ "inference engine not ready for parsed tt: " <> show x

-----------------
-- TT Calculus --
-----------------
-- How to handle Application of mixtures of types and terms
--ttApp :: _ -> Expr -> [Expr] -> TCEnv s Expr
ttApp readBind fn args = -- trace (clYellow (show fn <> " $ " <> show args)) $
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
        x  -> error $ "term applied to type: " <> show app <> show x
  Ty f -> case f of -- always a type family
    -- TODO match arities ?
    [THFam f a ixs] -> pure $ Ty [THFam f (drop (length args) a) (ixs ++ args)]
--  x -> pure $ Ty [THFam f [] args]
    x -> error $ "ttapp panic: " <> show x <> " $ " <> show args
  _ -> error $ "ttapp: not a function: " <> show fn <> " $ " <> show args
