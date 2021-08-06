-- see "Algebraic subtyping" by Stephen Dolan https://www.cl.cam.ac.uk/~sd601/thesis.pdf
module Infer where
import Prim
import BiUnify
import qualified ParseSyntax as P
import CoreSyn as C
import CoreUtils
import TypeCheck
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
    deBruijn' <- MV.new 0
    wip'      <- MV.replicate nBinds WIP
    fieldsV   <- MV.replicate nFields Nothing
    labelsV   <- MV.replicate nLabels Nothing
    bis'      <- MV.new nArgs
    [0 .. nArgs-1] `forM_` \i -> MV.write bis' i (BiSub [] [] 0 0)
--  domain'   <- MV.new nArgs

    st <- execStateT (judgeBind `mapM_` [0 .. nBinds-1]) $ TCEnvState
      {
        _pBinds   = pBinds'
      , _bisubNoSubtype = []
      , _bindWIP  = 0
      , _externs  = exts
      , _wip      = wip'
      , _bis      = bis'
      , _deBruijn = deBruijn'
      , _level    = Dominion (-1,-1)
      , _quants   = 0
      , _mus      = 0
      , _muEqui   = mempty
      , _fields   = fieldsV
      , _labels   = labelsV
      , _errors   = []
      }

    bis''    <- V.unsafeFreeze (st ^. bis)
    wip''    <- V.unsafeFreeze (st ^. wip)
    let domain'' = V.take nArgs bis''
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
    -- TODO guarantee that args are always consecutive !!

    ((tvarIdx , jb , ms) , resultTy) <- withBiSubs 1 $ \idx -> do
      MV.write wip' bindINm (Guard [] args idx)
      svLvl <- use level
      level .= Dominion (snd (tVarRange svLvl) + 1, snd (tVarRange svLvl))
      expr <- infer tt
      let jb = case expr of
            Core x ty -> case args of
              [] -> Core x ty
              ars-> Core (Abs (zip ars ((\x->[THVar x]) <$> args)) mempty x ty) ty
            t -> t
      bindWIP .= svwip
      Guard ms _ars tVar <- MV.read wip' bindINm
      pure (idx , jb , ms)

    cd <- use level
    MV.write wip' bindINm (Mutual cd jb False tvarIdx)
    if minimum (bindINm:ms) == bindINm then fromJust . head <$> generaliseBinds bindINm ms else pure jb
-- Check annotation if given
--bindTy <- maybe (pure genTy) (\ann -> checkAnnotation ann genTy mainArgTys (V.fromList argTys)) tyAnn

generaliseBinds i ms = use wip >>= \wip' -> do
  let getMutual m = do
        Mutual cd naiveExpr isRec recTVar <- MV.read wip' m
        pure (m , recTVar , cd , naiveExpr)
      substVars = \(m , recTVar , cd , naiveExpr) -> let
        Dominion (bStart , bEnd) = cd -- current dominion
        traceVars = pure () --use bis >>= \b -> [0..MV.length b -1] `forM` \i -> MV.read b i >>= \e -> traceM (show i <> " = " <> show e)
        in do
        done <- case did_ $ naiveExpr of
          Core expr coreTy -> let
            ty = case expr of -- inferrence produces the return type of Abs, ignoring arguments
              Abs ars free x fnTy -> addArrowArgs ((\(x,_t)->[THVar x]) <$> ars) coreTy
              _ -> coreTy
            in do
            traceVars
            -- check for recursive type
            use bis >>= \v -> MV.read v recTVar <&> _mSub >>= \case
              [] -> BiEQ <$ MV.write v recTVar (BiSub ty [] 0 0)
              t  -> biSub ty [THVar recTVar] -- ! recursive expression
            Core expr <$> substTVars recTVar
          t -> pure t
        done <$ MV.write wip' m (BindOK done)
  mutuals <- (i : ms) `forM` getMutual -- Usually a singleton list
  (mutuals `forM` substVars) <* (quants .= 0) <* (mus .= 0)

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
  -- ? Prefer user's type annotation over the inferred one
  -- ! we may have inferred some missing information
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
    [] -> if pos then [THBot] else [THTop] -- [] -> incQuants >>= \q -> pure [THBound q]
    t  -> t

  -- non-polar variables that reference nothing (or themselves) become forall quantified
  rmGuards = filter $ \case { THVarLoop v -> False; _->True }
  shouldGeneralise pos bisub@(BiSub pty mty pq mq) = (if pos then mq else pq) > 0
  generaliseVar pos vars v bisub@(BiSub pty mty pq mq) = let incQuants = quants <<%= (+1) in incQuants >>= \q -> do
    when global_debug $ traceM $ show v <> " " <> show pos <> " =∀" <> show q <> " " <> show bisub
    MV.modify vars (\(BiSub p m qp qm) -> BiSub (THBound q:rmGuards p) (THBound q:rmGuards m) qp qm) v
    -- Co-occurence analysis ?
--  case (if pos then pty else mty , if pos then mty else pty) of
--    ([] , t) -> t `forM` \case
--      THVar i -> MV.modify vars (\(BiSub p m qp qm) ->
--            BiSub (THBound q:rmGuards p) (THBound q:rmGuards m) qp qm) i
--      THVarLoop i -> MV.modify vars (\(BiSub p m qp qm) ->
--            BiSub (THBound q:rmGuards p) (THBound q:rmGuards m) qp qm) i
--    _ -> pure []
    (if pos then _pSub else _mSub) <$> MV.read vars v

  addPiBound pos vars v = MV.read vars v >>= \bisub ->
    if shouldGeneralise pos bisub then generaliseVar pos vars v bisub
    else d_ (show v <> show pos <> show bisub :: Text) $ pure []

  subst pos ty = nullLattice pos <$> let
    addMu d r v = (MV.read d v <&> if pos then _pSub else _mSub) <&> \case
      [THMuBound m] -> [THMu m r]
      _ -> r
    in use bis >>= \b -> do
    svMu <- use mus
    (vars , guardedTs) <- substVs pos ty

    case guardedTs of
      -- (Unguarded) loop: if any of these vars is generalised, they should all be generalised to the same THBound
      [THVarLoop n] -> do
        bs <- (\v -> (v,) <$> MV.read b v) `mapM` vars
        case find (shouldGeneralise pos . snd) bs of
          Nothing -> pure []
          Just (first , bisub) -> do
            q <- use quants
            v <- generaliseVar pos b first bisub
            vars `forM` \i -> MV.modify b (\(BiSub p m qp qm) ->
              BiSub (THBound q:rmGuards p) (THBound q:rmGuards m) qp qm) i
            pure v
      _  -> do
        vars  `forM` \x -> MV.modify b   (over (if pos then pSub else mSub) (const [THVarGuard x])) x
        t <- concatTypes <$> mapM (substTyHead pos) guardedTs
        mus .= svMu
        r <- foldM (addMu b) t vars -- TODO should only be one Mu !!
        vars  `forM` \x -> MV.modify b (\(BiSub p m qp qm) -> if pos then BiSub [THVar x] m qp qm else BiSub p [THVar x] qp qm) x
         --over (if pos then pSub else mSub) (const [THVar x])) x
        pure r

  -- We need to distinguish unguarded type variable loops (recursive type | indistinguishable vars)
  -- [a , b , c] var loops are all the same var; so if one is generalised, need to gen all of them
  substVs pos ty = let
    fn (v,o) = \case
      THVar x -> (x:v,o)
      x       -> (v,x:o)
    x@(vars , other) = foldl fn ([],[]) ty
    in if null vars then pure ([],ty) else
      use bis >>= \b -> do
      r <- (\(v,t) -> (v,mergeTypes t other)) <$> substV pos vars
--    traceShowM r
      pure r

  -- Check if type variables were already guarded (ie. we're in a recursive type)
  substV pos vars = let getTy = if pos then _pSub else _mSub in
    use bis >>= \b -> do
    varTypes <- vars `forM` \x -> (getTy <$> MV.read b x) >>= \t -> case t of --d_ (show x <> show t :: Text) t of
      []             -> (Nothing,) <$> addPiBound pos b x
      [THVarGuard v] -> pure (Nothing , t)
      _              -> (Just x,t) <$ MV.modify b (over (if pos then pSub else mSub) ((const [THVarLoop x]))) x
    let ts = snd <$> varTypes
        v' = catMaybes $ fst <$> varTypes
        varsTy = concatTypes ts

    (v,t) <- substVs pos varsTy
    pure (v'++v,t)

  substTyHead pos ty = let
    subst' = subst pos
    getTy = if pos then _pSub else _mSub
    in use bis >>= \b -> case ty of
    -- TODO ! add all vars in the loop as the same pi-bound
    THVarLoop x -> addPiBound pos b x

    THVarGuard v -> mus <<%= (+1) >>= \m -> let mb = [THMuBound m] in
      mb <$ MV.modify b (over (if pos then pSub else mSub) (const mb)) v
    THArrow ars ret -> do -- THArrow changes polarity => make sure not to miss quantifying vars in the result-type
      ret `forM` \case
        THVar x -> dupVar True x
        x -> pure ()
--    ars `forM` \x -> x `forM` \case
--      THVar x -> dupVar False x
--      x -> pure ()
      (\arsTy retTy -> [THArrow arsTy retTy]) <$> subst (not pos) `mapM` ars <*> subst' ret
    THTuple   tys -> (\x->[THTuple x])   <$> (subst' `traverse` tys)
    THProduct tys -> (\x->[THProduct x]) <$> (subst' `traverse` tys)
    THSumTy   tys -> (\x->[THSumTy   x]) <$> (subst' `traverse` tys)
    THBi b ty -> (\t->[THBi b t]) <$> subst' ty
    THMu b ty -> (\t->[THMu b t]) <$> subst' ty
    t -> pure [t]
--  t@THPrim{}  -> pure [t]
--  t@THBound{} -> pure [t]
--  t@THMuBound{}-> pure [t]
--  t@THTop{} -> pure [t]
--  t@THBot{} -> pure [t]
--  t@THExt{} -> pure [t]
--  t -> error $ show t --pure [t]
  in do --use bis >>= \b -> do
  let ty = [THVar recTVar]
  when global_debug $ traceM $ toS $ "Subst: " <> prettyTyRaw ty
  rawGenTy <- subst True ty
  q <- use quants
  let genTy = if q > 0 then [THBi q rawGenTy] else rawGenTy
  when global_debug $ traceM (toS $ prettyTyRaw genTy)
  pure genTy

infer :: P.TT -> TCEnv s Expr
infer = let
  -- App is the only place typechecking can fail
  -- f x : biunify [Df n Dx]tx+ under (tf+ <= tx+ -> a)
 biUnifyApp fTy argTys = do
   (biret , [retV]) <- withBiSubs 1 (\idx -> biSub_ fTy (addArrowArgs argTys [THVar idx]))
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
      use bis >>= \v-> MV.modify v (\(BiSub a b qa qb) -> BiSub a b (qa) (qb)) l

      pure $ Core (Var $ VArg l) [THVar l]
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
    -- TODO args should always be consecutive !!
    infer tt <&> \case
      Core x ty -> case args of
        [] -> Core x ty
        ars-> let
          fnTy = addArrowArgs ((\x->[THVar x]) <$> ars) ty
          in Core (Abs (zip ars ((\x->[THVar x]) <$> args)) mempty x fnTy) ty
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
        (_bs , [retTy]) <- withBiSubs 1 $ \ix -> biSub recordTy (mkExpected [THVar ix])
        pure $ Core (TTLens f fields LensGet) [THVar retTy]
--    P.LensSet x  -> infer x >>= \ammo -> let expect = mkExpected (tyOfExpr ammo)
--      in biSub recordTy [THProduct IM.empty] $> Core (TTLens f fields (LensSet ammo)) expect
      P.LensSet x  -> do
        (ammo , [retVar]) <- withBiSubs 1 $ \ix -> do
          ammo <- infer x
          let expect = mkExpected (tyOfExpr ammo)
          -- TODO don't overwrite foralls within expect
          biSub [THBi 1 [THArrow [[THBound 0 , THProduct mempty]] (THBound 0 : expect)]] [THArrow [recordTy] [THVar ix]]
          pure ammo
        pure $ Core (TTLens f fields (LensSet ammo)) [THVar retVar]

      P.LensOver x -> infer x >>= \fn -> do
        (bs , [tyOld, tyNew]) <- withBiSubs 2 $ \ ix -> do
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
          argTys   = (\i -> [THVar i]) <$> argNames
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
