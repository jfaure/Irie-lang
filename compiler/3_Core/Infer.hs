-- : see "Algebraic subtyping" by Stephen Dolan https://www.cl.cam.ac.uk/~sd601/thesis.pdf
module Infer where
import Prim
import BiUnify
import qualified ParseSyntax as P
import CoreSyn as C
import Errors
import CoreUtils
import TypeCheck
import TCState
import PrettyCore
import DesugarParse -- (matches2TT)
import Externs
import Mixfix
import Substitute

import Control.Lens
import Data.List (unzip4, foldl1, span , zipWith3)
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Mutable as MV
import qualified Data.Map.Strict as M
import qualified Data.IntMap as IM
import qualified Data.Text as T

formatError srcNames srcInfo (BiSubError o (TmpBiSubError failType got exp)) = let
  bindSrc = Just srcNames
  msg = let
    getName names q = if unQName q < 0
      then "!" <> show (0 - unQName q)
      else show (modName q) <> "." <> (names V.! modName q V.! unQName q)
    in case failType of
    TextMsg m     -> m
    TyConMismatch -> "Type constructor mismatch"
    AbsentField q -> "Absent field '" <> getName (srcFieldNames srcNames) q <> "'"
    AbsentLabel q -> "Absent label '" <> getName (srcLabelNames srcNames) q <> "'"

  srcLoc = case srcInfo of
    Nothing -> ""
    Just (SrcInfo text nlOff) -> let
      lineIdx = (\x -> x - 2) $ fromMaybe (0) $ VU.findIndex (> o) nlOff
      line    = (nlOff VU.! lineIdx)
      col     = o - line - 1
      in if lineIdx < 0
         then " <no source info>"
         else "\n" <> show lineIdx <> ":" <> show col <> ": \"" <> T.takeWhile (/= '\n') (T.drop o text) <> "\""
  in 
     "\n" <> clRed ("No subtype: " <> msg <> ":")
  <> srcLoc
  <> "\n      " <> clGreen (prettyTy bindSrc got)
  <> "\n  <:? " <> clGreen (prettyTy bindSrc exp)

formatCheckError bindSrc (CheckError inferredTy annTy) = clRed "Incorrect annotation: "
  <>  "\n  inferred: " <> clGreen (prettyTy (Just bindSrc) inferredTy)
  <>  "\n  expected: " <> clGreen (prettyTy (Just bindSrc) annTy)

formatScopeError = \case
  ScopeError h -> clRed "Not in scope: "      <> h
  AmbigBind  h -> clRed "Ambiguous binding: " <> h

judgeModule nBinds pm modIName nArgs hNames exts source = let
  modName = pm ^. P.moduleName
  nArgs   = pm ^. P.parseDetails . P.nArgs
  nFields = M.size (pm ^. P.parseDetails . P.fields)
  nLabels = M.size (pm ^. P.parseDetails . P.labels)
  pBinds' = V.fromListN nBinds (pm ^. P.bindings)
  in runST $ do
    deBruijn' <- MV.new 0
    wip'      <- MV.replicate nBinds WIP
    bis'      <- MV.new nArgs
    [0 .. nArgs - 1] `forM_` \i -> MV.write bis' i (BiSub [] [] 0 0)

    st <- execStateT (judgeBind `mapM_` [0 .. nBinds-1]) $ TCEnvState
      { _pBinds   = pBinds'
      , _externs  = exts
      , _thisMod  = modIName

      , _wip      = wip'
      , _biFails  = []
      , _scopeFails = []
      , _checkFails = []

      , _lvl      = 0
      , _srcRefs  = source
      , _tmpFails = []
      , _bindWIP  = 0
      , _blen     = nArgs
      , _bis      = bis'
      , _deBruijn = deBruijn'
      , _quants   = 0
      , _liftMu   = Nothing
      , _mus      = 0
      , _muEqui   = mempty
      , _muNest   = mempty
      , _deadVars = 0
      , _normFields = argSort nFields (pm ^. P.parseDetails . P.fields)
      , _normLabels = argSort nLabels (pm ^. P.parseDetails . P.labels)
      }

    bis''    <- V.unsafeFreeze (st ^. bis)
    wip''    <- V.unsafeFreeze (st ^. wip)
    let domain'' = V.take nArgs bis''
    pure $ (JudgedModule modName nArgs hNames (pm ^. P.parseDetails . P.fields) (pm ^. P.parseDetails . P.labels) wip''
          , TCErrors (st ^. scopeFails) (st ^. biFails) (st ^. checkFails))

-- inference >> generalisation >> type checking of annotations
-- Warning. this handles mutual binds and stacks inference of forward references
judgeBind :: IName -> TCEnv s Expr
judgeBind bindINm = use thisMod >>= \modINm -> use wip >>= \wip' -> (wip' `MV.read` bindINm) >>= \case
  BindOK e -> pure e
  Mutual e isRec tvar tyAnn -> pure (Core (Var (VQBind $ mkQName modINm bindINm)) [THVar tvar]) -- pure e

  Guard mutuals ars tvar -> do
    this <- use bindWIP
    when (this /= bindINm) $ do
      MV.write wip' bindINm (Guard (this:mutuals) ars tvar)
      MV.modify wip' (\(Guard ms ars tv) -> Guard (bindINm:ms) ars tv) this
    pure $ Core (Var (VQBind $ mkQName modINm bindINm)) [THVar tvar]

  WIP -> use wip >>= \wip' -> do
    svwip <- bindWIP <<.= bindINm
    let getTT (P.FunBind (P.FnDef hNm isTop letRecT mf implicits freeVars matches tyAnn)) = let
          (mainArgs , mainArgTys , tt) = matches2TT False matches
          args = sort $ (map fst implicits) ++ mainArgs -- TODO don't sort ; parser should always give sorted argnames
          in (tt , args , isTop , tyAnn)
    (tt , args , isTop , tyAnn) <- getTT . (V.! bindINm) <$> use pBinds

    ((tvarIdx , jb , ms) , resultTy) <- withBiSubs 1 $ \idx -> do
--    traceM $ "recIdx: " <> show idx
      MV.write wip' bindINm (Guard [] args idx)

      -- deadVars .= repeat bl 1 (1111..)
      -- we're entering a deeper let-nest; all existing tvars must be ignored while that is inferred
      -- TODO deeper tvars leaking upwards in biunify?
      sv <- use deadVars
--    use blen >>= \bl -> (deadVars .= setNBits (bl - 1)) -- TODO what consequences?
--    Note. this messed up forward declarations since later defs won't be substituted
      expr <- infer tt

--    TODO should we eagerly substitute let expressions ?
--    this could be an issue if THBounds are inserted in there
--    deadVars .= (if isTop then sv else setBit sv idx)

      let arTys = (\x->[THVar x]) <$> args
          jb = case expr of
            Core x ty -> let fnTy = prependArrowArgs arTys ty in case args of
              []  -> Core x ty
              ars -> Core (Abs (zip ars arTys) mempty x fnTy) fnTy
            t -> t
      bindWIP .= svwip
      Guard ms _ars tVar <- MV.read wip' bindINm
      pure (idx , jb , ms)

    -- get the Maybe type annotation
    typeAnn <- case tyAnn of
      Nothing -> pure Nothing
      Just t  -> (tyExpr <$> infer t) >>= \t -> case t of
        Nothing -> pure Nothing --error $ "not a type: " <> show t
        t       -> pure t

    MV.write wip' bindINm (Mutual jb False tvarIdx typeAnn)
    if minimum (bindINm:ms) == bindINm then fromJust . head <$> generaliseBinds bindINm ms else pure jb
-- Check annotation if given
--bindTy <- maybe (pure genTy) (\ann -> checkAnnotation ann genTy mainArgTys (V.fromList argTys)) tyAnn

generaliseBinds i ms = use wip >>= \wip' -> do
  let getMutual m = do
        Mutual naiveExpr isRec recTVar tyAnn <- MV.read wip' m
        pure (m , recTVar , naiveExpr , tyAnn)
      substVars = \(m , recTVar , naiveExpr , annotation) -> let
        traceVars= when global_debug $ use bis >>= \b -> [0..MV.length b -1] `forM_` \i -> MV.read b i >>= \e -> traceM (show i <> " = " <> show e)
        in do
        inferred <- case naiveExpr of
          Core expr coreTy -> do
            ty <- case expr of
              Abs ars free x fnTy -> pure $ coreTy --prependArrowArgs ((\(x,_t)->[THVar x]) <$> ars) coreTy
              _ -> pure coreTy
            -- check for recursive type
            use bis >>= \v -> MV.read v recTVar <&> _mSub >>= \case
              [] -> BiEQ <$ MV.write v recTVar (BiSub ty [] 0 0)
              t  -> biSub ty [THVar recTVar] -- ! recursive expression
            traceVars
            Core expr <$> substTVars recTVar
          t -> pure t
        done <- case (annotation , inferred) of
          (Just t , Core e inferredTy) -> Core e <$> checkAnnotation t inferredTy
          _                            -> pure inferred
        done <$ MV.write wip' m (BindOK done)
  mutuals <- (i : ms) `forM` getMutual -- Usually a singleton list
  (mutuals `forM` substVars) <* (quants .= 0) <* (mus .= 0)

checkAnnotation :: Type -> Type {--> [[P.TT]] -> V.Vector Type-} -> TCEnv s Type
checkAnnotation annTy inferredTy {-mainArgTys argTys-} = do
  exts <- use externs
  unless (check exts mempty mempty inferredTy annTy)
        (checkFails %= (CheckError inferredTy annTy:))

  -- ? Prefer user's type annotation (esp type aliases) over the inferred one
  -- ! we may have inferred some missing information
  -- type families (gadts) are special: we need to insert the list of labels as retTy
  pure $ case getRetTy inferredTy of
    s@[THFam{}] -> case flattenArrowTy annTy of
      [THArrow d r] -> [THFam r d []]
      x -> s
    _ -> annTy

infer :: P.TT -> TCEnv s Expr
infer = let
  -- App is the only place typechecking can fail
  -- f x : biunify [Df n Dx]tx+ under (tf+ <= tx+ -> a)
 biUnifyApp fTy argTys = do
   (biret , [retV]) <- withBiSubs 1 (\idx -> biSub_ fTy (prependArrowArgs argTys [THVar idx]))
   pure $ (biret , [THVar $ retV])
 retCast rc tt = case rc of { BiEQ -> tt ; c -> case tt of { Core f ty -> Core (Cast c f) ty } }

 checkFails srcOff x = use tmpFails >>= \case
   [] -> pure x
   x  -> PoisonExpr <$ (tmpFails .= []) <* (biFails %= (map (BiSubError srcOff) x ++))

 inferApp srcOff f args = let
   setRetTy retTy biret castArgs = \case -- ! we must set the retTy since ttApp doesn't
     Core (App f args) _ -> case biret of
       CastApp ac (Just pap) rc -> -- partial application
         retCast rc (Core (App (Instr (MkPAp (length pap))) (f : castArgs args biret)) retTy)
       CastApp ac Nothing    rc -> retCast rc (Core (App f (castArgs args biret)) retTy)
       _ -> Core (App f args) retTy
     Core f _ -> Core f retTy
     t -> t
   -- TODO This will let slip some bieq casts on function arguments
   castArg (a :: Term) = \case { BiEQ -> a ; CastApp [BiEQ] Nothing BiEQ -> a ; cast -> Cast cast a }
   castArgs args' cast = case cast of
     CastApp ac maybePap rc -> zipWith castArg args' (ac ++ repeat BiEQ) -- supplement paps with bieqs
     BiEQ -> args'
     x    -> _
   in do
     (biret , retTy) <- biUnifyApp (tyOfExpr f) (tyOfExpr <$> args)
     use tmpFails >>= \case
       [] -> setRetTy retTy biret castArgs <$> ttApp judgeBind f args
       x  -> trace ("problem fn: " <> show f :: Text) $ PoisonExpr <$ (tmpFails .= []) <* (biFails %= (map (\biErr -> BiSubError srcOff biErr) x ++))

 -- TODO don't allow `bind = lonemixfixword`
 handleExtern = let mfwOK = True in \case
   ForwardRef b       -> judgeLocalBind b -- was a forward reference not an extern
   Imported e         -> pure $ e
   NotInScope  h      -> PoisonExpr <$ (scopeFails %= (ScopeError h:))
   AmbiguousBinding h -> PoisonExpr <$ (scopeFails %= (AmbigBind h :))
   MixfixyVar m       -> if mfwOK then pure $ MFExpr m
     else PoisonExpr <$ (scopeFails %= (AmbigBind "mfword cannot be a binding" :))

 judgeLocalBind b = use thisMod >>= \modINm -> judgeBind b <&> \case
   Core e ty -> Core (Var $ VQBind $ mkQName modINm b) ty -- don't inline the body ! (
   t -> t

 judgeLabel qNameL exprs = use thisMod <&> \modINm -> let
   labTy = [THTyCon $ THTuple $ V.fromList $ tyOfExpr <$> exprs]
   in Core (Label qNameL exprs) [THTyCon $ THSumTy $ IM.singleton (qName2Key qNameL) labTy]

 in \case
  P.WildCard -> pure $ Core Question []
  P.Var v -> case v of -- vars : lookup in appropriate environment
    P.VLocal l     -> pure $ Core (Var (VArg l)) [THVar l]
    P.VBind b      -> judgeLocalBind b -- polytype env
    P.VExtern i    -> use externs >>= \e -> handleExtern (readParseExtern e i)

  P.Foreign i tt   -> infer tt <&> \case
    PoisonExpr -> PoisonExpr
    ty         -> Core (Var (VForeign i)) (fromMaybe (error $ "not a type: " <> show ty) (tyExpr ty))
  P.ForeignVA i tt -> infer tt <&> \case
    PoisonExpr -> PoisonExpr
    ty         -> Core (Var (VForeign i)) (fromMaybe (error $ "not a type: " <> show ty) (tyExpr ty))

  P.Abs top -> let
    -- unlike topBind, don't bother generalising the type
      getTT (P.FunBind (P.FnDef hNm False letRecT mf implicits freeVars matches tyAnn)) = let
        (mainArgs , mainArgTys , tt) = matches2TT False matches
        args = {-sort $-} (map fst implicits) ++ mainArgs -- TODO don't sort !
        in (tt , args)
      (tt , args) = getTT top
    in do
    -- TODO args should always be consecutive !!
    infer tt <&> \case
      Core x ty -> case args of
        []  -> Core x ty
        args -> let
          argVars = (\x->[THVar x]) <$> args
          fnTy    = prependArrowArgs argVars ty
          in Core (Abs (zip args argVars) mempty x fnTy) fnTy
      t -> t

  P.App fTT argsTT -> infer fTT >>= \f -> (infer `mapM` argsTT) >>= inferApp (-1) f
  P.Juxt srcOff juxt -> let
    inferExprApp srcOff = \case
      ExprApp fE [] -> panic "impossible: empty expr App"
      ExprApp fE argsE -> inferExprApp srcOff fE >>= \case
        Core (Label iLabel ars) _ -> (inferExprApp srcOff `mapM`  argsE) >>= judgeLabel iLabel
        f -> (inferExprApp srcOff `mapM`  argsE) >>= inferApp srcOff f
      QVar q -> use externs >>= \e -> handleExtern (readQParseExtern e (modName q) (unQName q))
      MFExpr{}   -> PoisonExpr <$ (scopeFails %= (AmbigBind "mixfix word":))
      core -> pure core
    in (solveMixfixes <$> (infer `mapM` juxt)) >>= inferExprApp srcOff

  P.Cons construct -> use thisMod >>= \modINm -> use externs >>= \ext -> do
    let (fieldsLocal , rawTTs) = unzip construct
        fields = qName2Key . readField ext {-mkQName modINm-} <$> fieldsLocal
    exprs <- infer `mapM` rawTTs
    let (tts , tys) = unzip $ (\case { Core t ty -> (t , ty) ; x -> error $ show x }) <$> exprs
        poison = (\case { PoisonExpr -> True ; _ -> False }) `any` exprs
        mkFieldCol = \a b -> [THFieldCollision a b]
    pure $ if poison
      then PoisonExpr
      else Core (Cons (IM.fromList $ zip fields tts)) [THTyCon $ THProduct (IM.fromListWith mkFieldCol $ zip fields tys)]

  P.TTLens o tt fieldsLocal maybeSet -> use thisMod >>= \modINm -> use externs >>= \ext -> infer tt >>= \record -> let
      fields = readField ext {-mkQName modINm-} <$> fieldsLocal
      recordTy = tyOfExpr record
      mkExpected :: Type -> Type
      mkExpected dest = foldr (\fName ty -> [THTyCon $ THProduct (IM.singleton (qName2Key fName) ty)]) dest fields
    in (>>= checkFails o) $ case record of
    e@(Core f gotTy) -> case maybeSet of
      P.LensGet    -> withBiSubs 1 (\ix -> biSub recordTy (mkExpected [THVar ix]))
        <&> \(cast , [retTy]) -> Core (TTLens (Cast cast f) fields LensGet) [THVar retTy]

      P.LensSet x  -> infer x <&> \case -- LeafTy -> Record -> Record & { path : LeafTy }
        new@(Core newLeaf newLeafTy) -> Core (TTLens f fields (LensSet new)) (gotTy ++ mkExpected newLeafTy)
        _ -> PoisonExpr

      P.LensOver x -> infer x >>= \fn -> do
         let [singleField] = fields
         ((ac , rc , outT , rT) , {-[tyOld, tyNew, output]-} _) <- withBiSubs 3 $ \ ix -> let
           inT = [THVar ix] ; outT = [THVar (ix+1)] ; rT  = THVar (ix + 2)
           in do -- need 3 fresh TVars since we cannot assume anything about the "fn" or the "record" type
           argCast <- biSub (tyOfExpr fn) [THTyCon $ THArrow [inT] outT] <&> \case
             CastApp [argCast] pap BiEQ  -> argCast -- pap ?
             BiEQ                        -> BiEQ
           -- note. the typesystem does not atm support quantifying over field presences
           rCast <- biSub recordTy (rT : mkExpected inT)
           pure (argCast , rCast , outT , rT)
--       traceShowM (ac , rc , outT , rT)

         let lensOverCast = case rc of
               CastProduct drops [(asmIdx,cast)] -> Cast (CastOver asmIdx ac fn outT) f
               BiEQ -> f
               x -> error $ "expected CastProduct: " <> show rc

--       pure $ Core lensOverCast (THVar output : mkExpected outT)
         pure $ Core lensOverCast (rT : mkExpected outT)

    PoisonExpr -> pure PoisonExpr
    t -> error $ "record type must be a term: " <> show t

  P.Label localL tts -> use externs >>= \ext -> (infer `mapM` tts) >>= judgeLabel (readLabel ext localL)

  -- Sumtype declaration
  P.TySum alts -> use thisMod >>= \modINm -> use externs >>= \ext -> do -- alts are function types
    -- 1. Check against ann (retTypes must all subsume the signature)
    -- 2. Create sigma type from the arguments
    -- 3. Create proof terms from the return types
    let go (l,ty,Nothing)      = pure (qName2Key (readLabel ext l {- mkQName modINm l-}) , [])
        go (l,ty,Just (impls,gadt)) = (qName2Key (readLabel ext l {- mkQName modINm l-}),) <$> (mkSigma (map fst impls) =<< infer ty)
        mkSigma impls ty = do
          ty' <- expr2Ty judgeBind ty
          pure $ case impls of
            [] -> ty'
            impls -> [THPi $ Pi (map (,[THSet 0]) impls) ty']
    sumArgsMap <- go `mapM` alts
    let sumTy = [THTyCon $ THSumTy $ IM.fromListWith (\a b -> [THFieldCollision a b]) sumArgsMap]
        returnTypes = getFamilyTy . snd <$> sumArgsMap
        getFamilyTy x = case getRetTy x of -- TODO currying ?
--        [THRecSi m ars] -> [THArrow (take (length ars) $ repeat [THSet 0]) sumTy]
          [THRecSi m ars] -> [THFam sumTy (take (length ars) $ repeat [THSet 0]) []]
          x -> sumTy
        dataTy = foldl1 mergeTypes $ returnTypes
    pure $ Ty sumTy

  P.Match alts catchAll -> use thisMod >>= \modINm -> use externs >>= \ext -> let
    -- * desugar all patterns in the alt fns
    -- * mk tuples out of those abstractions to represent the sum type
    -- * ret type is a join of all the abs ret tys
    desugarFns = \(lname , free , pats , tt) -> let
      (args , _ , e) = patterns2TT False pats tt
      in (qName2Key (readLabel ext lname {-mkQName modINm lname-}) , args , _ , e)
    (labels , args , _ , exprs) = unzip4 $ (desugarFns <$> alts)
    in do
    alts <- infer `mapM` exprs
    let poison = (\case { PoisonExpr -> True ; _ -> False }) `any` alts
        altTys  = tyOfExpr <$> alts
        retTy   = foldl mergeTypes [] altTys
        altTys' = map (\altArgs -> [THTyCon$ THTuple $ V.fromList (arg2ty <$> altArgs)]) args
        scrutTy = [THTyCon $ THSumTy $ IM.fromList $ zip labels altTys']
        matchTy = [mkTyArrow [scrutTy] retTy]
        arg2ty i= [THVar i]
        argAndTys  = map (map (\x -> (x , arg2ty x))) args
        altsMap = let
          addAbs ty (Core t _) args = Core (Abs args mempty t []) ty
          addAbs ty PoisonExpr _ = PoisonExpr
          in IM.fromList $ zip labels (zipWith3 addAbs altTys alts argAndTys)
    pure $ if poison then PoisonExpr else
      Core (Match retTy altsMap Nothing) matchTy

  P.LitArray literals -> let
    ty = typeOfLit (fromJust $ head literals) -- TODO merge (join) all tys ?
    in pure $ Core (Lit . Array $ literals) [THTyCon $ THArray [ty]]

  P.Lit l  -> pure $ Core (Lit l) [typeOfLit l]

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
       { [a , b] -> Ty [mkTyArrow [a] b] }
     Instr (TyInstr MkIntN) -> case args of
       [Core (Lit (Int i)) ty] -> pure $ Ty [THPrim (PrimInt $ fromIntegral i)]
     coreFn -> doApp coreFn args
   Ty f -> case f of -- always a type family
     -- TODO match arities ?
     [THFam f a ixs] -> pure $ Ty [THFam f (drop (length args) a) (ixs ++ args)]
--   x -> pure $ Ty [THFam f [] args]
     x -> error $ "ttapp panic: " <> show x <> " $ " <> show args
   _ -> error $ "ttapp: not a function: " <> show fn <> " $ " <> show args
