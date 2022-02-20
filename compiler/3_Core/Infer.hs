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
import Generalise --Substitute

import Control.Lens
import Data.List (unzip4, span , zipWith3)
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
  <> "\n      " <> clGreen (toS $ prettyTy ansiRender{ bindSource = bindSrc } got)
  <> "\n  <:? " <> clGreen (toS $ prettyTy ansiRender{ bindSource = bindSrc } exp)

formatCheckError bindSrc (CheckError inferredTy annTy) = clRed "Incorrect annotation: "
  <>  "\n  inferred: " <> clGreen (prettyTy (ansiRender { bindSource = Just bindSrc }) inferredTy)
  <>  "\n  expected: " <> clGreen (prettyTy (ansiRender { bindSource = Just bindSrc }) annTy)

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
    wip'      <- MV.replicate nBinds WIP
    bis'      <- MV.new 0
--  bis'      <- MV.replicate 1 (BiSub [] [])
    argVars'  <- MV.new nArgs
    biEqui'   <- MV.replicate nBinds (complement 0)

    st <- execStateT (judgeBind `mapM_` [0 .. nBinds-1]) $ TCEnvState
      { _pBinds   = pBinds'
      , _externs  = exts
      , _thisMod  = modIName

      , _wip        = wip'
      , _biFails    = []
      , _scopeFails = []
      , _checkFails = []

      , _argVars  = argVars'
      , _bindWIP  = 0
      , _tmpFails = []
      , _blen     = 0
      , _bis      = bis'
      , _quants   = 0
      , _quantsRec= 0
      , _biEqui   = biEqui'
      , _coOccurs = _
      , _escapedVars = 0
      , _leakedVars  = 0
      , _deadVars    = 0
      , _muWrap      = Nothing
      , _recVars     = 0
      , _hasRecs     = 0
--    , _normFields = argSort nFields (pm ^. P.parseDetails . P.fields)
--    , _normLabels = argSort nLabels (pm ^. P.parseDetails . P.labels)
      }

    bis''    <- V.unsafeFreeze (st ^. bis)
    wip''    <- V.unsafeFreeze (st ^. wip)
    pure $ (JudgedModule modIName modName nArgs hNames (pm ^. P.parseDetails . P.fields) (pm ^. P.parseDetails . P.labels) wip''
          , TCErrors (st ^. scopeFails) (st ^. biFails) (st ^. checkFails))

-- inference >> generalisation >> type checking of annotations
-- This stacks inference of forward references and handles mutual binds
judgeBind :: IName -> TCEnv s Expr
judgeBind bindINm = use thisMod >>= \modINm -> use wip >>= \wip' -> (wip' `MV.read` bindINm) >>= \case
  BindOK e -> pure e
  Mutual e freeVs isRec tvar tyAnn -> pure (Core (Var (VQBind $ mkQName modINm bindINm)) (TyVar tvar)) -- pure e

  Guard mutuals tvar -> do
    this <- use bindWIP
    when (this /= bindINm) $ do
      MV.write wip' bindINm (Guard (this:mutuals) tvar)
      MV.modify wip' (\(Guard ms tv) -> Guard (bindINm:ms) tv) this
    pure $ Core (Var (VQBind $ mkQName modINm bindINm)) (TyVar tvar)

  WIP -> use wip >>= \wip' -> do
    abs   <- (V.! bindINm) <$> use pBinds
    svwip <- bindWIP <<.= bindINm
    let freeVars = P.fnFreeVars (P.fnDef abs)
        tyAnn    = P.fnSig (P.fnDef abs)
    freeTVars <- use argVars >>= \avs -> bitSet2IntList freeVars `forM` \i -> MV.read avs i
    svEscapes <- escapedVars <<%= (.|. intList2BitSet freeTVars)
    svLeaked  <- use leakedVars

    (tvarIdx , jb , ms) <- freshBiSubs 1 >>= \[idx] -> do
      MV.write wip' bindINm (Guard [] idx)
      expr <- infer (P.Abs abs)
      bindWIP .= svwip
      Guard ms tVar <- MV.read wip' bindINm
      pure (idx , expr , ms)

    -- get the Maybe type annotation
    typeAnn <- case tyAnn of
      Nothing -> pure Nothing
      Just t  -> (tyExpr <$> infer t) >>= \t -> case t of
        Nothing -> pure Nothing --error $ "not a type: " <> show t
        t       -> pure t

    MV.write wip' bindINm (Mutual jb freeVars False tvarIdx typeAnn)
    if minimum (bindINm:ms) /= bindINm then pure jb
    else (fromJust . head <$> generaliseBinds svEscapes svLeaked bindINm ms)

generaliseBinds :: BitSet -> BitSet -> Int -> [Int] -> TCEnv s [Expr]
generaliseBinds svEscapes svLeaked i ms = use wip >>= \wip' -> (i : ms) `forM` \m ->
  MV.read wip' m >>= \(Mutual naiveExpr freeVs isRec recTVar annotation) -> do
  inferred <- case naiveExpr of
    Core expr coreTy -> Core expr <$> do -- generalise the type
      (ty , free) <- case expr of
        Abs ars free x fnTy -> pure (coreTy , free)
        _ -> pure (coreTy , freeVs)
      -- rec / mutual: if this bind : τ was used within itself , something bisubed with -τ
      use bis >>= \v -> MV.read v recTVar <&> _mSub >>= \case
        TyGround [] -> BiEQ <$ MV.write v recTVar (BiSub ty (TyGround []))
        t           -> bisub ty (TyVar recTVar) -- ! this binding is recursive | mutual
      bl <- use blen
      when global_debug $ use bis >>= \b -> [0..bl -1] `forM_`
        \i -> MV.read b i >>= \e -> traceM (show i <> " = " <> show e)
      freeArgTVars <- use argVars >>= \argPerms -> bitSet2IntList freeVs `forM` \i -> MV.read argPerms i
      escaped <- use escapedVars
--    when (free == 0) (leakedVars .= 0) --svLeaked)
      generalise escaped recTVar <* when (free == 0) (clearBiSubs recTVar)
    t -> pure t
  l <- use leakedVars
  leakedVars  .= svLeaked
  escapedVars .= svEscapes
  deadVars %= (.|. (l .&. complement svEscapes))
  done <- case (annotation , inferred) of
    (Just t , Core e inferredTy) -> Core e <$> checkAnnotation t inferredTy
    _                            -> pure inferred
  done <$ MV.write wip' m (BindOK done)

checkAnnotation :: Type -> Type {--> [[P.TT]] -> V.Vector Type-} -> TCEnv s Type
checkAnnotation annTy inferredTy {-mainArgTys argTys-} = do
  exts <- use externs
  unless (check exts mempty mempty inferredTy annTy)
        (checkFails %= (CheckError inferredTy annTy:))

  -- ? Prefer user's type annotation (esp type aliases) over the inferred one
  -- ! we may have inferred some missing information
  -- type families (gadts) are special: we need to insert the list of labels as retTy
  pure annTy
--  pure $ case getRetTy inferredTy of
----  s@[THFam{}] -> case flattenArrowTy annTy of
----    [THArrow d r] -> [THFam r d []]
----    x -> s
--    _ -> annTy

infer :: P.TT -> TCEnv s Expr
infer = let
 addArgTVars args = use argVars >>= \argPerms -> let
    nArgs = length args
    mkArgVars = (\i -> TyVar i)
   in map mkArgVars <$> (freshBiSubs nArgs >>= \argTVars -> zipWithM (\a v -> v <$ MV.write argPerms a v) args argTVars)

  -- App is the only place typechecking can fail
 biUnifyApp fTy argTys = freshBiSubs 1 >>= \[retV] ->
   (, TyVar retV) <$> bisub fTy (prependArrowArgsTy argTys (TyVar retV))
   
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
   in if any (\case {PoisonExpr{}->True ; _->False}) (f : args) then pure PoisonExpr else do
     (biret , retTy) <- biUnifyApp (tyOfExpr f) (tyOfExpr <$> args)
     use tmpFails >>= \case
       [] -> setRetTy retTy biret castArgs <$> ttApp judgeBind f args
       x  -> PoisonExpr <$ -- trace ("problem fn: " <> show f :: Text)
          ((tmpFails .= []) *> (biFails %= (map (\biErr -> BiSubError srcOff biErr) x ++)))

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

 judgeLabel qNameL exprs = let
   labTy = TyGround [THTyCon $ THTuple $ V.fromList $ tyOfExpr <$> exprs]
   in Core (Label qNameL exprs) (TyGround [THTyCon $ THSumTy $ IM.singleton (qName2Key qNameL) labTy])

 in \case
  P.WildCard -> pure $ Core Question (TyGround [])
  P.Var v -> case v of -- vars : lookup in appropriate environment
    P.VLocal l     -> use argVars >>= (`MV.read` l) <&> \t -> Core (Var (VArg l)) (TyVar t) -- [THVar l]
    P.VBind b      -> judgeLocalBind b
    P.VExtern i    -> use thisMod >>= \mod -> use externs >>= \e -> handleExtern (readParseExtern mod e i)

  P.Foreign i tt   -> infer tt <&> \case
    PoisonExpr -> PoisonExpr
    ty         -> Core (Var (VForeign i)) (fromMaybe (error $ "not a type: " <> show ty) (tyExpr ty))
  P.ForeignVA i tt -> infer tt <&> \case
    PoisonExpr -> PoisonExpr
    ty         -> Core (Var (VForeign i)) (fromMaybe (error $ "not a type: " <> show ty) (tyExpr ty))

  P.Abs (P.FunBind (P.FnDef hNm isTop letRecT mf implicits freeVars matches tyAnn)) -> let
    (mainArgs , mainArgTys , tt) = matches2TT False matches
    args = (fst <$> implicits) ++ mainArgs
    in do
    argTVars  <- addArgTVars args
    infer tt <&> \case
      Core x ty -> case args of
        []  -> Core x ty
        args -> let
          fnTy    = prependArrowArgsTy argTVars ty
          in Core (Abs (zip args argTVars) freeVars x fnTy) fnTy
      t -> t

  P.App fTT argsTT -> infer fTT >>= \f -> (infer `mapM` argsTT) >>= inferApp (-1) f
  P.Juxt srcOff juxt -> let
    inferExprApp srcOff = \case
      ExprApp fE [] -> panic "impossible: empty expr App"
      ExprApp fE argsE -> inferExprApp srcOff fE >>= \case
        Core (Label iLabel ars) _ -> (inferExprApp srcOff `mapM`  argsE) <&> judgeLabel iLabel
        f -> (inferExprApp srcOff `mapM`  argsE) >>= inferApp srcOff f
      QVar q -> use thisMod >>= \modIName -> use externs >>= \e ->
        handleExtern (readQParseExtern modIName e (modName q) (unQName q))
      MFExpr{}   -> PoisonExpr <$ (scopeFails %= (AmbigBind "mixfix word":))
      core -> pure core
    in (solveMixfixes <$> (infer `mapM` juxt)) >>= inferExprApp srcOff

  P.Cons construct -> use externs >>= \ext -> do
    let (fieldsLocal , rawTTs) = unzip construct
        fields = qName2Key . readField ext <$> fieldsLocal
    exprs <- infer `mapM` rawTTs
    let (tts , tys) = unzip $ (\case { Core t ty -> (t , ty) ; x -> error $ show x }) <$> exprs
        poison = (\case { PoisonExpr -> True ; _ -> False }) `any` exprs
        mkFieldCol = \a b -> TyGround [THFieldCollision a b]
        retTycon = THProduct (IM.fromListWith mkFieldCol $ zip fields tys)
    pure $ if poison
      then PoisonExpr
      else Core (Cons (IM.fromList $ zip fields tts)) (TyGround [THTyCon retTycon])

  P.TTLens o tt fieldsLocal maybeSet -> use externs >>= \ext -> infer tt >>= \record -> let
      fields = readField ext <$> fieldsLocal
      recordTy = tyOfExpr record
      mkExpected :: Type -> Type
      mkExpected dest = foldr (\fName ty -> TyGround [THTyCon $ THProduct (IM.singleton (qName2Key fName) ty)]) dest fields
    in (>>= checkFails o) $ case record of
    e@(Core f gotTy) -> case maybeSet of
      P.LensGet    -> freshBiSubs 1 >>= \[i] -> bisub recordTy (mkExpected (TyVar i))
        <&> \cast -> Core (TTLens (Cast cast f) fields LensGet) (TyVar i)

      P.LensSet x  -> infer x <&> \case -- LeafTy -> Record -> Record & { path : LeafTy }
        new@(Core newLeaf newLeafTy) -> Core (TTLens f fields (LensSet new)) (gotTy `mergeTypes` mkExpected newLeafTy)
        _ -> PoisonExpr

      P.LensOver x -> infer x >>= \fn -> do
         let [singleField] = fields
         (ac , rc , outT , rT) <- freshBiSubs 3 >>= \[inI , outI , rI] -> let
           inT = TyVar inI ; outT = TyVar outI
           in do -- need 3 fresh TVars since we cannot assume anything about the "fn" or the "record" type
           argCast <- bisub (tyOfExpr fn) (TyGround [THTyCon $ THArrow [inT] outT]) <&> \case
             CastApp [argCast] pap BiEQ  -> argCast -- pap ?
             BiEQ                        -> BiEQ
           -- note. the typesystem does not atm support quantifying over field presences
           rCast <- bisub recordTy (mergeTVar rI (mkExpected inT))
--         rCast <- bisub recordTy (rT : mkExpected inT)
           pure (argCast , rCast , outT , rI)
--       traceShowM (ac , rc , outT , rT)

         let lensOverCast = case rc of
               CastProduct drops [(asmIdx,cast)] -> Cast (CastOver asmIdx ac fn outT) f
               BiEQ -> f
               x -> error $ "expected CastProduct: " <> show rc

         pure $ Core lensOverCast (mergeTVar rT (mkExpected outT))

    PoisonExpr -> pure PoisonExpr
    t -> error $ "record type must be a term: " <> show t

  P.Label localL tts -> use externs >>= \ext -> (infer `mapM` tts) <&> judgeLabel (readLabel ext localL)

  -- Sumtype declaration
{-
  P.TySum alts -> use externs >>= \ext -> do -- alts are function types
    -- 1. Check against ann (retTypes must all subsume the signature)
    -- 2. Create sigma type from the arguments
    -- 3. Create proof terms from the return types
    let go (l,ty,Nothing)      = pure (qName2Key (readLabel ext l) , [])
        go (l,ty,Just (impls,gadt)) = (qName2Key (readLabel ext l),) <$> (mkSigma (map fst impls) =<< infer ty)
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
--        [THRecSi m ars] -> [THFam sumTy (take (length ars) $ repeat [THSet 0]) []]
          x -> sumTy
        dataTy = foldl1 mergeTypes $ returnTypes
    pure $ Ty sumTy
-}

  P.Match alts catchAll -> use externs >>= \ext -> let
    -- * desugar all patterns in the alt fns
    -- * mk tuples out of those abstractions to represent the sum type
    -- * ret type is a join of all the abs ret tys
    desugarFns = \(lname , free , pats , tt) -> let
      (args , _ , e) = patterns2TT False pats tt
      in (qName2Key (readLabel ext lname) , args , _ , e)
    (labels , args , _ , exprs) = unzip4 $ (desugarFns <$> alts)
    in do
    argTVars <- addArgTVars `mapM` args
    alts <- infer `mapM` exprs
    let poison = (\case { PoisonExpr -> True ; _ -> False }) `any` alts
        altTys  = tyOfExpr <$> alts
        retTy   = mergeTypeList altTys
        altTys' = map (\argTVars -> TyGround [THTyCon$ THTuple $ V.fromList argTVars]) argTVars
        scrutTy = TyGround [THTyCon $ THSumTy $ IM.fromList $ zip labels altTys']
        matchTy = TyGround $ mkTyArrow [scrutTy] retTy
        argAndTys  = zipWith zip args argTVars
        altsMap = let
          addAbs ty (Core t _) args = Core (Abs args 0 t ty) ty
          addAbs ty PoisonExpr _ = PoisonExpr
          in IM.fromList $ zip labels (zipWith3 addAbs altTys alts argAndTys)
    pure $ if poison then PoisonExpr else
      Core (Match retTy altsMap Nothing) matchTy

  -- TODO merge (join) all the tys to produce the array ?
--P.LitArray literals -> let
--  ty = TyGround [typeOfLit (fromJust $ head literals)]
--  in pure $ Core (Lit . Array $ literals) (TyGround [THTyCon $ THArray ty])

  P.Lit l  -> pure $ Core (Lit l) (TyGround [typeOfLit l])

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
     [] -> Core app _ -- don't forget to set retTy
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
       { [a , b] -> Ty (TyGround (mkTyArrow [a] b)) }
     Instr (TyInstr MkIntN) -> case args of
       [Core (Lit (Int i)) ty] -> pure $ Ty (TyGround [THPrim (PrimInt $ fromIntegral i)])
     coreFn -> doApp coreFn args
   Ty f -> case f of -- always a type family
     -- TODO match arities ?
--   [THFam f a ixs] -> pure $ Ty [THFam f (drop (length args) a) (ixs ++ args)]
--   x -> pure $ Ty [THFam f [] args]
     x -> error $ "ttapp panic: " <> show x <> " $ " <> show args
   _ -> error $ "ttapp: not a function: " <> show fn <> " $ " <> show args
