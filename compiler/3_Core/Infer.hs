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
import Data.List (unzip4, zipWith3, foldl1, span)
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
    fieldsV   <- MV.replicate nFields Nothing
    labelsV   <- MV.replicate nLabels Nothing
    [0 .. nArgs-1] `forM_` \i -> MV.write domain' i (BiSub [] [] 0 0)

    st <- execStateT (judgeBind `mapM_` [0 .. nBinds-1]) $ TCEnvState
      {
        _pBinds   = pBinds'
      , _bindWIP  = 0
      , _externs  = exts
      , _wip      = wip'
      , _bis      = bis'
      , _deBruijn = deBruijn'
      , _level    = Dominion (-1,-1)
      , _quants   = 0
      , _mus      = 0
      , _muEqui   = mempty
      , _domain   = domain'
      , _fields   = fieldsV
      , _labels   = labelsV
      , _errors   = []
      }

    bis''    <- V.unsafeFreeze (st ^. bis)
    domain'' <- V.unsafeFreeze (st ^. domain)
    wip''    <- V.unsafeFreeze (st ^. wip)
    pure $ JudgedModule hNames wip'' bis'' mempty{- qtt''-} domain''

-- generalisation (and therefore type checking of usertypes) happens here
judgeBind :: IName -> TCEnv s Expr
judgeBind bindINm = use wip >>= \wip' -> (wip' `MV.read` bindINm) >>= \case
  BindOK e   -> pure e
  Mutual d e isRec tvar -> pure e

  Guard mutuals ars tvar -> do
    this <- use bindWIP
    when (this /= bindINm) $ do
      MV.write wip' bindINm (Guard (this:mutuals) ars tvar)
      MV.modify wip' (\(Guard ms ars tv) -> Guard (bindINm:ms) ars tv) this
    pure $ Core (Var (VBind bindINm)) [THVar tvar] -- [THRec bindINm]

  WIP -> use wip >>= \wip' -> do
    svwip <- bindWIP <<.= bindINm
    let getTT (P.FunBind hNm implicits freeVars matches tyAnn) = let
          (mainArgs , mainArgTys , tt) = matches2TT matches
          args = sort $ (map fst implicits) ++ mainArgs -- TODO don't sort !
          in (tt , args)
    (tt , args) <- getTT . (V.! bindINm) <$> use pBinds
    traceShowM args -- TODO args should always be consecutive !!

    ((tvarIdx , jb , ms) , resultTy) <- withBiSubs 1 $ \idx -> do
      -- dup True [THVar idx] *> biSub_ fTy (addArrowArgs argTys [THVar idx]))
      MV.write wip' bindINm (Guard [] args idx)
      svLvl <- use level
      level .= Dominion (snd (tVarRange svLvl) + 1, snd (tVarRange svLvl))
      expr <- infer tt
      let jb = case expr of
            Core x ty -> case args of
              [] -> Core x ty
              ars-> Core (Abs (zip ars ((\x->[THArg x]) <$> args)) mempty x ty) ty
            t -> t
      bindWIP .= svwip
      Guard ms _ars tVar <- MV.read wip' bindINm
      pure (idx , jb , ms)

    cd <- use level
    MV.write wip' bindINm (Mutual cd jb False tvarIdx)
    if (minimum (bindINm:ms) == bindINm) then fromJust . head <$> generaliseBinds bindINm ms else pure jb
-- Check annotation if given
--bindTy <- maybe (pure genTy) (\ann -> checkAnnotation ann genTy mainArgTys (V.fromList argTys)) tyAnn

generaliseBinds i ms = use wip >>= \wip' -> do
  let getArs = \case { Core (Abs ars free x ty) t -> (fst <$> ars) ; _->[] }
      getMutual m = do
        Mutual cd naiveExpr isRec recTVar <- MV.read wip' m -- if isrec
        pure (recTVar , m , getArs naiveExpr , cd , naiveExpr)
      substVars = \(recTVar , m , args , cd , naiveExpr) ->
        let Dominion (bStart , bEnd) = cd -- current dominion
            traceTVars range b = range `forM_` \i -> MV.read b i >>= \s -> traceM (show i <> ": " <> show s :: Text)
            traceVars = do
              traceM $ "gen: " <> show args <> " , " <> show cd
              use bis    >>= traceTVars [bStart - 1 .. bEnd]
              traceM "-- ^ TVars v TArgs"
              use domain >>= traceTVars args
        in do

        done <- case naiveExpr of
          Core (Abs ars free x _ty) ty -> do -- TODO add mu bind to the return type
            let argTys = (\(x,_t)->[THArg x]) <$> ars
            biSub (addArrowArgs argTys ty) [THVar recTVar]
            traceVars
            g <- substTVars recTVar
            pure $ Core (Abs ars free x g) g -- $ mergeTypes merge g
          Core expr ty -> do
            biSub ty [THVar recTVar]
            traceVars
            Core expr <$> substTVars recTVar
          t -> pure t
        done <$ MV.write wip' m (BindOK done)
  mutuals <- (i : ms) `forM` getMutual -- Usually a singleton list
  (mutuals `forM` substVars) <* (quants .= 0)
 
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

-- substTVars: recursively substitute type vars, insert foralls and μ binders, simplify types
-- Simplifications:
--  * remove polar variables `a&int -> int` => int->int ; `int -> a` => `int -> bot`
--  * unify inseparable variables (co-occurence `a&b -> a|b` and indistinguishables `a->b->a|b`)
--  * remove variables that contain the same upper and lower bound (a<:t and t<:a)`a&int->a|int`
--  * roll up recursive types
substTVars recTVar = let
  concatTypes = foldl mergeTypes []
  nullLattice pos = \case
    [] -> pure $ if pos then [THTop] else [THBot] -- [] -> incQuants >>= \q -> pure [THBound q]
    t  -> pure t

  -- non-polar variables that reference nothing (or themselves) become forall quantified
  addPiBound pos vars v = MV.read vars v >>= \bisub@(BiSub pty mty pq mq) -> let
    incQuants = quants <<%= (+1) -- add a forall quantified THBound variable
--  in case did_ (if pos then mty else pty) of
--  [THBound x] -> pure [THBound x]
--  _ ->
    in d_ (show v <> " " <> show pos <> ": " <> show bisub :: Text) $ case if pos then mq else pq of
      0 -> pure []
      nonZ -> incQuants >>= \q -> do
        traceM $ show v <> " " <> show pos <> " =∀" <> show q <> " lam@ " <> show bisub
        -- TODO rm only the appropriate guard
        let rmGuards = filter $ \case { THArgGuard v->False ; THVarGuard v->False ; _->True }
        MV.modify vars (\(BiSub p m qp qm) -> did_ $ BiSub (THBound q:rmGuards p) (THBound q:rmGuards m) qp qm) v
        (if pos then _pSub else _mSub) <$> MV.read vars v

  rmGuards = filter $ \case { THArgGuard v->False ; THVarGuard v->False ; THVarLoop v->False ; THArgLoop v->False;_->True }
  subst pos ty = let
    addMu d r v = (MV.read d v <&> if pos then _pSub else _mSub) <&> \case
      [THMuBound m] -> [THMu m r]
      _ -> r
    in use domain >>= \dom -> use bis >>= \b -> do
    (vars , avars , guardedTs) <- {-did_ <$> -}substVs pos ty

    traceShowM (pos , vars , avars , guardedTs)
    vars  `forM` \x -> MV.modify b   (over (if pos then pSub else mSub) (const [THVarGuard x])) x
    avars `forM` \x -> MV.modify dom (over (if pos then pSub else mSub) (const [THArgGuard x])) x
    t <- concatTypes <$> mapM (substTyHead pos) guardedTs
    t1 <- foldM (addMu dom) t avars
    foldM (addMu b) t1 vars

  -- We need to distinguish unguarded type variable loops (recursive type | indistinguishable vars)
  -- [a , b , c] var loops are all the same var; so if one is generalised, need to gen all of them
  substVs pos ty = let
    fn (v,a,o) = \case
      THVar x -> (x:v,a,o)
      THArg x -> (v,x:a,o)
      x       -> (v,a,x:o)
    x@(vars , avars , other) = foldl fn ([],[],[]) ty
    in if null vars && null avars then pure ([],[],ty) else
      use domain >>= \dom -> use bis >>= \b -> do
      r <- (\(v,a,t) -> (v,a,mergeTypes t other)) <$> substV pos vars avars
      traceShowM r
      pure r

  -- If a type variable was already guarded (ie. we're in a recursive type), don't touch it
  substV pos vars avars = let getTy = if pos then _pSub else _mSub in
    use domain >>= \dom -> use bis >>= \b -> do
    varTypes <- vars `forM` \x -> (getTy <$> MV.read b x) >>= \t -> case t of
      []             -> (Nothing,) <$> addPiBound pos b x
      [THVarGuard v] -> pure (Nothing , t)
      _              -> (Just x,t) <$ MV.modify b (over (if pos then pSub else mSub) ((const [THVarLoop x]))) x
    argTypes <- avars `forM` \x -> (getTy <$> MV.read dom x) >>= \t -> case t of
      []             -> (Nothing,) <$> addPiBound pos dom x
      [THArgGuard v] -> pure (Nothing , t)
      _              -> (Just x,t) <$ MV.modify dom (over (if pos then pSub else mSub) (const [THArgLoop x])) x
    let ts = snd <$> (varTypes ++ argTypes)
        v' = catMaybes $ fst <$> varTypes
        a' = catMaybes $ fst <$> argTypes
        varsTy = concatTypes ts

    (v,a,t) <- substVs pos varsTy
    pure (v'++v,a'++a,t)

  substTyHead pos ty = let
    subst' = subst pos
    getTy = if pos then _pSub else _mSub
    in use domain >>= \dom -> use bis >>= \b -> case ty of
    -- TODO ! add all vars in the loop as the same pi-bound
    THVarLoop x -> addPiBound pos b x
    THArgLoop x -> addPiBound pos dom x

    THArgGuard v -> [THMuBound v]
      <$ MV.modify dom (over (if pos then pSub else mSub) (const [THMuBound v])) v
    THVarGuard v -> [THMuBound (1-v)]
      <$ MV.modify b (over (if pos then pSub else mSub) (const [THMuBound (1-v)])) v
    THArrow ars ret -> (\arsTy retTy -> [THArrow arsTy retTy]) <$> subst (not pos) `mapM` ars <*> subst' ret
    THTuple   tys -> (\x->[THTuple x])   <$> (subst' `traverse` tys)
    THProduct tys -> (\x->[THProduct x]) <$> (subst' `traverse` tys)
    THSumTy   tys -> (\x->[THSumTy   x]) <$> (subst' `traverse` tys)
    THBi b ty -> (\t->[THBi b t]) <$> subst' ty
    THMu b ty -> (\t->[THMu b t]) <$> subst' ty
    t@THPrim{}  -> pure [t]
    t@THBound{} -> pure [t]
    t@THMuBound{}-> pure [t]
    t -> error $ show t --pure [t]
  in do --use bis >>= \b -> do
  let ty = [THVar recTVar]
  traceM $ toS $ "Subst: " <> prettyTyRaw ty
  rawGenTy <- subst True ty
  q <- use quants
  let genTy = if q > 0 then [THBi q rawGenTy] else rawGenTy
  traceM (toS $ prettyTyRaw genTy)
  pure genTy

infer :: P.TT -> TCEnv s Expr
infer = let
  -- App is the only place typechecking can fail
  -- f x : biunify [Df n Dx]tx+ under (tf+ <= tx+ -> a)
 biUnifyApp fTy argTys = do
-- dup False `mapM` argTys
   (biret , [retV]) <- withBiSubs 1 (\idx -> dup True [THVar idx] *> biSub_ fTy (addArrowArgs argTys [THVar idx]))
   pure $ (biret , [THVar retV])

 in \case
  P.WildCard -> pure $ Core Hole [THSet 0]

  P.Var v -> let
      judgeLocalBind b = judgeBind b <&> \case
        Core e ty -> Core (Var $ VBind b) ty -- don't copy the body
        t -> t
    in case v of -- vars : lookup in appropriate environment
    P.VBind b   -> judgeLocalBind b -- polytype env
    P.VLocal l  -> do -- monotype env (fn args)
--    _+ 1 to +qtt, also yolo _+ 1 to -qtt in case this is a funciton type (not ideal)
      use domain >>= \v-> MV.modify v (\(BiSub a b qa qb) -> BiSub a b (1+qa) (qb)) l

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
    args <- infer `mapM` argsTT
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

  P.TTLens tt fields maybeSet -> infer tt >>= \record -> let
      recordTy = tyOfExpr record
      mkExpected :: Type -> Type
      mkExpected dest = foldr (\fName ty -> [THProduct (IM.singleton fName ty)]) dest fields
    in case record of
    Core f _ -> case maybeSet of
      P.LensGet    -> do -- for get, we need a typevar for the destination
        (_bs , [retTy]) <- withBiSubs 1 $ \ix -> dup True [THVar ix] *> biSub recordTy (mkExpected [THVar ix])
        pure $ Core (TTLens f fields LensGet) [THVar retTy]
--    P.LensSet x  -> infer x >>= \ammo -> let expect = mkExpected (tyOfExpr ammo)
--      in biSub recordTy [THProduct IM.empty] $> Core (TTLens f fields (LensSet ammo)) expect
      P.LensSet x  -> do
        (ammo , [retVar]) <- withBiSubs 1 $ \ix -> dup True [THVar ix] *> do
          ammo <- infer x
          let expect = mkExpected (tyOfExpr ammo)
          -- TODO don't overwrite foralls within expect
          biSub [THBi 1 [THArrow [[THBound 0 , THProduct mempty]] (THBound 0 : expect)]] [THArrow [recordTy] [THVar ix]]
          pure ammo
        pure $ Core (TTLens f fields (LensSet ammo)) [THVar retVar]

      P.LensOver x -> infer x >>= \fn -> do
        (bs , [tyOld, tyNew]) <- withBiSubs 2 $ \ ix -> do
          dup False [THVar (ix+1)]
          dup True [THVar ix]
          biSub [THArrow [[THVar ix]] [THVar (ix+1)]] (tyOfExpr fn)
          biSub recordTy (mkExpected [THVar (ix+1)])
        pure $ Core (TTLens f fields (LensOver fn)) (mkExpected [THVar tyNew])
    t -> panic "record type must be a term" -- pure t

  -- TODO Set0 not general enough (want a forall (a : _))
  P.Label l tts -> infer `mapM` tts <&> \exprs -> let
    -- label return type could be anything of type label (?!)
--  labTy = addArrowArgs (tyOfExpr <$> exprs) [THSet 0] --[THPi $ Pi [(0,[])] [THBound 0]]
    labTy = [THTuple $ V.fromList $ tyOfExpr <$> exprs]
    in Core (Label l exprs) [THSumTy $ IM.singleton l labTy]

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
--  use labels >>= \labelsV -> sumArgsMap `forM` \(l,t) -> MV.write labelsV l (Just t)
    let --sumTy = [THSum $ fst <$> sumArgsMap]
        sumTy = [THSumTy $ IM.fromList sumArgsMap]
        returnTypes = getFamilyTy . snd <$> sumArgsMap
        getFamilyTy x = case getRetTy x of -- TODO currying ?
--        [THRecSi m ars] -> [THArrow (take (length ars) $ repeat [THSet 0]) sumTy]
          [THRecSi m ars] -> [THFam sumTy (take (length ars) $ repeat [THSet 0]) []]
          x -> sumTy
        dataTy = foldl1 mergeTypes $ returnTypes
    pure $ Ty sumTy

  P.Match alts -> let
      (altLabels , freeVars , patterns , rawTTs) = unzip4 alts
    -- * find the type of the sum type being deconstructed
    -- * find the type of it's alts (~ lambda abstractions)
    -- * type of Match is (sumTy -> Join altTys)
      mkFnTy vals = [THTuple $ V.fromList vals] -- \case { [] -> [THSet 0] ; x -> [THArrow (drop 1 x) [THSet 0]] }
      pattern2Ty = mkFnTy . \case
        [] -> []
        P.PArg _ : xs -> [THSet 0] : [pattern2Ty xs]
      tys = pattern2Ty <$> patterns
    in do
    altExprs <- infer `mapM` rawTTs
    let altTys = tyOfExpr <$> altExprs
    retTy <- foldl mergeTypes [] <$> pure altTys -- (tyOfExpr <$> altExprs)
    let unpat = \case { P.PArg i -> i ; x -> error $ "not ready for pattern: " <> show x }
        mkFn pat free (Core t tyAltRet) = let
          argNames = unpat <$> pat
          argTys   = (\i -> [THArg i]) <$> argNames
          args     = zip argNames argTys
          in (Core (Abs args free t tyAltRet) tyAltRet
             , [THTuple $ V.fromList argTys])
        (alts , altTys) = unzip $ zipWith3 mkFn patterns freeVars altExprs
        altLabelsMap = IM.fromList $ zip altLabels alts
        scrutTy = [THSumTy $ IM.fromList $ zip altLabels altTys] -- [THSplit altLabels]
        matchTy = [THArrow [scrutTy] retTy]
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
