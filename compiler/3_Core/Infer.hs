-- : see "Algebraic subtyping" by Stephen Dolan https://www.cl.cam.ac.uk/~sd601/thesis.pdf
module Infer where
import Prim
import BiUnify
import qualified ParseSyntax as P
import CoreSyn as C
import CoreUtils
import TypeCheck
import TCState
import PrettyCore
import DesugarParse (matches2TT)
import Externs
import Mixfix

import Control.Lens
import Data.List (unzip4, zipWith3, foldl1, span)
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Mutable as MV
import qualified Data.Map as M
import qualified Data.IntMap as IM
import qualified Data.Text as T

formatError srcInfo (BiSubError o (TmpBiSubError msg got exp)) = let
  srcLoc = case srcInfo of
    Nothing -> ""
    Just (SrcInfo text nlOff) -> let
      lineIdx = (\x -> x - 2) $ fromMaybe (0) $ VU.findIndex (> o) nlOff
      line    = (nlOff VU.! lineIdx)
      col     = o - line - 1
      in "\n" <> show lineIdx <> ":" <> show col <> ": \"" <> T.takeWhile (/= '\n') (T.drop o text) <> "\""
  in srcLoc
  <> "\n" <> clRed ("No subtype" <> if T.null msg then ":" else " (" <> msg <> "):")
  <> "\n      " <> clGreen (prettyTyRaw got)
  <> "\n  <:? " <> clGreen (prettyTyRaw exp)

formatScopeError = \case
  ScopeError h -> clRed "Not in scope: "      <> h
  AmbigBind  h -> clRed "Ambiguous binding: " <> h

judgeModule pm hNames exts source = let
  modName = pm ^. P.moduleName
  nBinds  = length $ pm ^. P.bindings
  nArgs   = pm ^. P.parseDetails . P.nArgs
  nFields = M.size (pm ^. P.parseDetails . P.fields)
  nLabels = M.size (pm ^. P.parseDetails . P.labels)
  pBinds' = V.fromListN nBinds (pm ^. P.bindings)
  argSort :: Int -> M.Map HName IName -> VU.Vector IName
  argSort n hmap = let v = VU.fromList (M.elems hmap) in VU.unsafeBackpermute v v
  in runST $ do
    deBruijn' <- MV.new 0
    wip'      <- MV.replicate nBinds WIP
    fieldsV   <- MV.replicate nFields Nothing
    labelsV   <- MV.replicate nLabels Nothing
    bis'      <- MV.new nArgs
    [0 .. nArgs - 1] `forM_` \i -> MV.write bis' i (BiSub [] [] 0 0)

    st <- execStateT (judgeBind `mapM_` [0 .. nBinds-1]) $ TCEnvState
      { _pBinds   = pBinds'
      , _externs  = exts

      , _wip      = wip'
      , _biFails  = []
      , _scopeFails = []

      , _srcRefs  = source
      , _tmpFails = []
      , _bindWIP  = 0
      , _bis      = bis'
      , _deBruijn = deBruijn'
      , _level    = Dominion (-1,-1)
      , _quants   = 0
      , _mus      = 0
      , _muEqui   = mempty
      , _normFields = argSort nFields (pm ^. P.parseDetails . P.fields)
      , _normLabels = argSort nLabels (pm ^. P.parseDetails . P.labels)
      }

    bis''    <- V.unsafeFreeze (st ^. bis)
    wip''    <- V.unsafeFreeze (st ^. wip)
    let domain'' = V.take nArgs bis''
    pure $ (JudgedModule modName hNames wip''
          , TCErrors (st ^. scopeFails) (st ^. biFails))

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
    pure $ Core (Var (VBind bindINm)) [THVar tvar]

  WIP -> use wip >>= \wip' -> do
    svwip <- bindWIP <<.= bindINm
    let getTT (P.FunBind (P.FnDef hNm letRecT mf implicits freeVars matches tyAnn)) = let
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
        traceVars = when global_debug $ use bis >>= \b -> [0..MV.length b -1] `forM_` \i -> MV.read b i >>= \e -> traceM (show i <> " = " <> show e)
        in do
        done <- case naiveExpr of
          Core expr coreTy -> do
            ty <- case expr of -- inferrence produces ret type of Abs, ignoring arguments
              Abs ars free x fnTy -> use bis >>= \v -> do
                -- TODO how general is this ?
                -- Idea is to ensure top level polyvars are marked (since won't pass bisub)
                ars `forM` \(x,_ty) -> (_mSub <$> MV.read v x) >>= \case
                  [] -> dupVar False x
                  _  -> pure () -- typevar will be substituted, don't mark it
                pure $ addArrowArgs ((\(x,_t)->[THVar x]) <$> ars) coreTy
              _ -> pure coreTy
            -- check for recursive type
            use bis >>= \v -> MV.read v recTVar <&> _mSub >>= \case
              [] -> BiEQ <$ MV.write v recTVar (BiSub ty [] 0 0)
              t  -> biSub ty [THVar recTVar] -- ! recursive expression
            traceVars
            Core expr <$> substTVars recTVar -- TODO overwrite Abs tys ?
          t -> pure t
        done <$ MV.write wip' m (BindOK done)
  mutuals <- (i : ms) `forM` getMutual -- Usually a singleton list
  (mutuals `forM` substVars) <* (quants .= 0) <* (mus .= 0)

checkAnnotation :: P.TT -> Type -> [[P.TT]] -> V.Vector Type -> TCEnv s Type
checkAnnotation ann inferredTy mainArgTys argTys = do
  ann <- tyExpr <$> infer ann
  let inferArg = \case { [x] -> tyExpr <$> infer x ; [] -> pure [THSet 0] }
  argAnns  <- inferArg `mapM` mainArgTys
  let annTy = case mainArgTys of { [] -> ann ; x  -> mkTyArrow argAnns ann }
  exts <- use externs
--labelsV <- V.freeze =<< use labels
  unless (check exts argTys mempty inferredTy annTy)
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
--  [] -> if pos then [THTop] else [THBot] -- [] -> incQuants >>= \q -> pure [THBound q]
    [] -> if pos then [THBot] else [THTop] -- [] -> incQuants >>= \q -> pure [THBound q]
    t  -> t

  -- non-polar variables that reference nothing (or themselves) become forall quantified
  rmGuards = filter $ \case { THVarLoop v -> False; _->True }
  shouldGeneralise pos bisub@(BiSub pty mty pq mq) = (if pos then mq else pq) > 0
  generaliseVar pos vars v bisub@(BiSub pty mty pq mq) = let incQuants = quants <<%= (+1) in incQuants >>= \q -> do
    when global_debug $ traceM $ show v <> " " <> show pos <> " =∀" <> show q <> " " <> show bisub
    MV.modify vars (\(BiSub p m qp qm) -> BiSub (THBound q:rmGuards p) (THBound q:rmGuards m) qp qm) v
    -- Co-occurence analysis ?
    (if pos then _pSub else _mSub) <$> MV.read vars v

  addPiBound pos vars v = MV.read vars v >>= \bisub ->
    if shouldGeneralise pos bisub then generaliseVar pos vars v bisub
    else pure [] --d_ (show v <> show pos <> show bisub :: Text) $ pure []

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
  substV pos vars = use bis >>= \b -> do
    varTypes <- vars `forM` \x -> MV.read b x >>= \bisub -> let
      t = if pos then _pSub bisub else _mSub bisub
      in case t of --d_ (show x <> show t :: Text) t of
      []             -> (Nothing,) <$> addPiBound pos b x
      [THVarGuard v] -> pure (Nothing , t)
      subbedTy       -> case if pos then _mSub bisub else _pSub bisub of
        -- Check the opposite polarity (if this variable's opposite will be generalised later, it can't be ignored now)
--      [] | (if pos then _mQ bisub else _pQ bisub) > 0 -> addPiBound pos b x <&> \thbound -> (Just x , thbound ++ subbedTy)
--      TODO use (not pos) ?
        [] -> addPiBound (pos) b x <&> \thbound -> (Just x , thbound ++ subbedTy)
        _  -> (Just x,t) <$ MV.modify b (over (if pos then pSub else mSub) ((const [THVarLoop x]))) x
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
    THTyCon t -> (\t -> [THTyCon t]) <$> case t of
      THArrow ars ret -> do -- THArrow changes polarity => make sure not to miss quantifying vars in the result-type
        ret `forM` \case
          THVar x -> dupVar pos x
          x -> pure ()
--      ars `forM` \x -> x `forM` \case
--        THVar x -> dupVar False x
--        x -> pure ()
        (\arsTy retTy -> THArrow arsTy retTy) <$> subst (not pos) `mapM` ars <*> subst' ret
      THTuple   tys -> THTuple   <$> (subst' `traverse` tys)
      THProduct tys -> THProduct <$> (subst' `traverse` tys)
      THSumTy   tys -> THSumTy   <$> (subst' `traverse` tys)
    THBi b ty -> (\t->[THBi b t]) <$> subst' ty
    THMu b ty -> (\t->[THMu b t]) <$> subst' ty
    t -> pure [t]
--  THPrim{}   -> pure [t]
--  THBound{}  -> pure [t]
--  THMuBound{}-> pure [t]
--  THTop{}    -> pure [t]
--  THBot{}    -> pure [t]
--  THExt{}    -> pure [t]
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
 retCast rc tt = case rc of { BiEQ -> tt ; c -> case tt of { Core f ty -> Core (Cast c f) ty } }

 checkFails o x = use tmpFails >>= \case
   [] -> pure x
   x  -> PoisonExpr <$ (tmpFails .= []) <* (biFails %= ((map (\biErr -> BiSubError o biErr) x ++)))

 inferApp o f args = let
   setRetTy retTy biret castArgs = \case -- ! we must set the retTy since ttApp doesn't
     Core (App f args) _ -> case biret of
       CastApp _ (Just pap) rc -> let -- handle PAp
         mkpap = Instr (MkPAp (length pap))
         in retCast rc (Core (App mkpap (f : castArgs args biret)) retTy)
       CastApp _ Nothing    rc -> retCast rc (Core (App f (castArgs args biret)) retTy)
       _ -> Core (App f args) retTy
     Core f _ -> Core f retTy
     t -> t
   in do
     (biret , retTy) <- biUnifyApp (tyOfExpr f) (tyOfExpr <$> args)
     let castArg (a :: Term) = \case { BiEQ -> a ; cast -> Cast cast a } -- \case { BiInstr f -> App (Instr f) [a] ; _ -> a }
         castArgs args' cast = case cast of
           CastApp ac maybePap rc -> zipWith castArg args' (ac ++ repeat BiEQ) -- TODO why not enough bisubs ?!
           x -> args'
     use tmpFails >>= \case
       [] -> setRetTy retTy biret castArgs <$> ttApp judgeBind f args
       x  -> PoisonExpr <$ (tmpFails .= []) <* (biFails %= (map (\biErr -> BiSubError o biErr) x ++))

 handleExtern = \case
   ForwardRef b       -> judgeLocalBind b -- was a forward reference not an extern
   Imported e         -> pure e
   NotInScope  h      -> PoisonExpr <$ (scopeFails %= (ScopeError h:))
   AmbiguousBinding h -> PoisonExpr <$ (scopeFails %= (AmbigBind h :))
   MixfixyVar m       -> pure $ MFExpr m

 judgeLocalBind b = judgeBind b <&> \case
   Core e ty -> Core (Var $ VBind b) ty -- no need to inline the body
   t -> t
 in \case
  P.WildCard -> pure $ Core Hole holeTy

  P.Var v -> case v of -- vars : lookup in appropriate environment
    P.VBind b   -> judgeLocalBind b -- polytype env
    P.VLocal l  -> pure $ Core (Var (VArg l)) [THVar l]
    P.VExtern i -> use externs >>= \e -> handleExtern (readParseExtern e i)

  P.Abs top -> let
    -- unlike topBind, don't bother generalising the type
      getTT (P.FunBind (P.FnDef hNm letRecT mf implicits freeVars matches tyAnn)) = let
        (mainArgs , mainArgTys , tt) = matches2TT matches
        args = sort $ (map fst implicits) ++ mainArgs -- TODO don't sort !
        in (tt , args)
      (tt , args) = getTT top
    in do
    -- TODO args should always be consecutive !!
    infer tt <&> \case
      Core x ty -> case args of
        []  -> Core x ty
        ars -> let
          fnTy = addArrowArgs ((\x->[THVar x]) <$> ars) ty
          in Core (Abs (zip ars ((\x->[THVar x]) <$> args)) mempty x fnTy) ty
      t -> t

  P.App fTT argsTT -> infer fTT >>= \f -> (infer `mapM` argsTT) >>= inferApp 0 f
  P.Juxt o juxt -> let
    inferExprApp o = \case
      ExprApp fE [] -> panic "impossible: empty expr App"
      ExprApp fE argsE -> inferExprApp o fE >>= \f -> (inferExprApp o `mapM`  argsE) >>= inferApp o f
      QVar (m,i) -> use externs >>= \e -> handleExtern (readQParseExtern e m i)
      core -> pure core
    in (solveMixfixes <$> (infer `mapM` juxt)) >>= inferExprApp o

  P.Cons construct -> do
    let (fields , rawTTs) = unzip construct
    exprs <- infer `mapM` rawTTs
    let (tts , tys) = unzip $ (\case { Core t ty -> (t , ty) }) <$> exprs
        mkFieldCol = \a b -> [THFieldCollision a b]
    pure $ Core (Cons (IM.fromList $ zip fields tts)) [THTyCon $ THProduct (IM.fromListWith mkFieldCol $ zip fields tys)]

  P.TTLens o tt fields maybeSet -> infer tt >>= \record -> let
      recordTy = tyOfExpr record
      mkExpected :: Type -> Type
      mkExpected dest = foldr (\fName ty -> [THTyCon $ THProduct (IM.singleton fName ty)]) dest fields
    in (>>= checkFails o) $ case record of
    e@(Core f _) -> case maybeSet of
      P.LensGet    -> withBiSubs 1 (\ix -> biSub recordTy (mkExpected [THVar ix]))
        <&> \(cast , [retTy]) -> Core (TTLens (Cast cast f) fields LensGet) [THVar retTy]

      P.LensSet x  -> error "todo set; use lensOver"

      P.LensOver x -> infer x >>= \fn -> do
        -- A -> B -> C -> C & { lensPath A } -> C & { lensPath B }
        ((expect , fieldCount , asmIdx , ac) , _tvars) <- withBiSubs 1 $ \ ix -> let
          retVar = [THVar ix]
          [f] = fields
          [THTyCon (THProduct recordMap)] = recordTy
          (Just leafTy , newMap) = IM.insertLookupWithKey (\k n o -> n) f retVar recordMap
          expect = [THTyCon $ THProduct newMap]
          in do
          -- retcast always bieq , since we gave it a fresh retvar ..
          argCast <- biSub (tyOfExpr fn) (mkTyArrow [leafTy] retVar) <&> \case
            CastApp [argCast] pap BiEQ  -> argCast
            BiEQ                        -> BiEQ
          -- resolving to asmIdx..  sadly need to re-sort all fields on normalised index
          -- ! do this at codegen
          nf <- use normFields
          let normalised = V.fromList $ IM.keys $ IM.mapKeys (nf VU.!) newMap
              Just asmIdx = V.findIndex (== nf VU.! f) normalised
          pure (expect , V.length normalised , asmIdx , argCast)
        let lensInput = case ac of
              BiEQ -> f
              cast -> Cast (CastProduct 0 $ zip ([0..]::[Int]) $ replicate asmIdx BiEQ ++ (ac : replicate (fieldCount - asmIdx - 1) BiEQ)) f
            leafAddr = (asmIdx , BiEQ) -- just need the field location, it was already casted by the product cast
        pure $ Core (TTLens lensInput fields (LensOver leafAddr fn)) expect

    PoisonExpr -> pure PoisonExpr
    t -> error $ "record type must be a term: " <> show t

  P.Label l tts -> infer `mapM` tts <&> \exprs -> let
    labTy = [THTyCon $ THTuple $ V.fromList $ tyOfExpr <$> exprs]
    in Core (Label l exprs) [THTyCon $ THSumTy $ IM.singleton l labTy]

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
    let sumTy = [THTyCon $ THSumTy $ IM.fromListWith (\a b -> [THFieldCollision a b]) sumArgsMap]
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
      mkFnTy vals = [THTyCon $ THTuple $ V.fromList vals] -- \case { [] -> [THSet 0] ; x -> [THArrow (drop 1 x) [THSet 0]] }
      pattern2Ty = mkFnTy . \case
        [] -> []
        P.PArg _ : xs -> [THSet 0] : [pattern2Ty xs]
      tys = pattern2Ty <$> patterns
    in do
    altExprs <- infer `mapM` rawTTs
    let altTys = tyOfExpr <$> altExprs
    retTy <- foldl mergeTypes [] <$> pure altTys -- (tyOfExpr <$> altExprs)
    let unpat = \case { P.PArg i -> i ; x -> error $ "not implemented: pattern: " <> show x }
        mkFn pat free (Core t tyAltRet) = let
          argNames = unpat <$> pat
          argTys   = (\i -> [THVar i]) <$> argNames
          args     = zip argNames argTys
          in (Core (Abs args free t tyAltRet) tyAltRet
             , [THTyCon $ THTuple $ V.fromList argTys])
        (alts , altTys) = unzip $ zipWith3 mkFn patterns freeVars altExprs
        altLabelsMap = IM.fromList $ zip altLabels alts
        scrutTy = [THTyCon $ THSumTy $ IM.fromList $ zip altLabels altTys] -- [THSplit altLabels]
        matchTy = mkTyArrow [scrutTy] retTy
    pure $ Core (Match retTy altLabelsMap Nothing) matchTy

  -- desugar --
  P.LitArray literals -> let
    ty = typeOfLit (fromJust $ head literals) -- TODO merge (join) all tys ?
    in pure $ Core (Lit . Array $ literals) [THTyCon $ THArray [ty]]

  P.Lit l  -> pure $ Core (Lit l) [typeOfLit l]
--  P.InfixTrain lArg train -> infer $ resolveInfixes (\_->const True) lArg train -- TODO
  x -> error $ "not implemented: inference of: " <> show x

-----------------
-- TT Calculus --
-----------------
-- How to handle Application of Exprs (mixture of types and terms)
ttApp :: (Int -> TCEnv s Expr) -> Expr -> [Expr] -> TCEnv s Expr
ttApp readBind fn args = let --trace (clYellow (show fn <> " $ " <> show args :: Text)) $ let
 ttApp' = ttApp readBind
 doApp coreFn args = let
   (ars , end) = span (\case {Core{}->True ; _->False}) args
   app = App coreFn $ (\(Core t _ty)->t) <$> ars -- drop argument types
   in pure $ case end of
     [] -> Core app [] -- don't forget to set retTy
     PoisonExpr : _ -> PoisonExpr
     x  -> error $ "term applied to type: " <> show app <> show x

 in case fn of
   PoisonExpr -> pure PoisonExpr
   ExprApp f2 args2 -> (ttApp' f2 args2) >>= \f' -> ttApp' f' args
   Core cf ty -> case cf of
--   Var (VBind i) -> readBind i >>= \e -> case e of
--     Core (Var (VBind j)) ty | j == i -> doApp (Var (VBind j)) args
--     f -> ttApp' f args
--   Instr (MkPAp n) -> case args of
--     f : args' -> ttApp' f args'
     Instr (TyInstr Arrow)  -> expr2Ty readBind `mapM` args <&> \case
       { [a , b] -> Ty $ mkTyArrow [a] b }
     Instr (TyInstr MkIntN) -> case args of
       [Core (Lit (Int i)) ty] -> pure $ Ty [THPrim (PrimInt $ fromIntegral i)]
     coreFn -> doApp coreFn args
   Ty f -> case f of -- always a type family
     -- TODO match arities ?
     [THFam f a ixs] -> pure $ Ty [THFam f (drop (length args) a) (ixs ++ args)]
--   x -> pure $ Ty [THFam f [] args]
     x -> error $ "ttapp panic: " <> show x <> " $ " <> show args
   _ -> error $ "ttapp: not a function: " <> show fn <> " $ " <> show args
