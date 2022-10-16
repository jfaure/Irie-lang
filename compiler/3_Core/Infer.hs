-- : see "Algebraic subtyping" by Stephen Dolan https://www.cs.tufts.edu/~nr/cs257/archive/stephen-dolan/thesis.pdf
module Infer (judgeModule) where
import Prim ( PrimInstr(MkPAp) )
import BiUnify ( bisub )
import qualified ParseSyntax as P
import CoreSyn as C
import CoreUtils ( isPoisonExpr, mergeTVar, mergeTypeList, mergeTypes, mkTyArrow, prependArrowArgsTy, tyExpr, tyOfExpr )
import TTCalculus ( ttApp )
import Scope
import Errors
import TypeCheck ( check )
import TCState
import Externs ( typeOfLit, readField, readLabel, readQParseExtern , Externs )
import Generalise ( generalise )

import Control.Lens
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV ( MVector, modify, new, read, write )
import qualified Data.Vector.Generic.Mutable as MV (unsafeGrowFront)
import qualified BitSetMap as BSM ( toList, fromList, fromListWith, singleton )
import Data.Functor.Foldable

judgeModule ∷ P.Module -> BitSet -> ModuleIName -> p -> V.Vector HName -> Externs.Externs -> p1 -> (JudgedModule , Errors)
judgeModule pm importedModules modIName _nArgs hNames exts _source = let
  modName   = pm ^. P.moduleName
  in runST $ do
    wip'      <- MV.new 0 -- V.unsafeThaw (Left <$> pm ^. P.bindings)
    letBinds' <- MV.new 10
    bis'      <- MV.new 64
    (modTT , st) <- runStateT (infer exts modIName importedModules emptyBitSet (pm ^. P.bindings)) TCEnvState
      { _externs  = exts
      , _thisMod  = modIName

      , _wip      = wip'
      , _letBinds = letBinds'
      , _letNest  = 0
      , _errors   = emptyErrors
      , _bruijnArgVars = mempty

      , _openModules = importedModules
      , _bindWIP  = (0 , False)
      , _tmpFails = []
      , _blen     = 0
      , _bis      = bis'
      , _escapedVars  = emptyBitSet
      , _leakedVars   = emptyBitSet
      , _deadVars     = emptyBitSet
      }
--  wip'' <- map ((\abs -> error "impossible") ||| identity) <$> V.unsafeFreeze (st ^. wip)
    pure (JudgedModule modIName modName hNames (pm ^. P.parseDetails . P.fields) (pm ^. P.parseDetails . P.labels)
      modTT Nothing , st ^. errors) --TCErrors (st ^. scopeFails) (st ^. biFails) (st ^. checkFails))

-- infer >> generalise >> check annotation
-- This stacks inference of forward references + let-binds and handles mutuals (only generalise at end of mutual block)
-- This includes noting leaked and escaped typevars
judgeBind :: MV.MVector s (Either P.FnDef Bind) -> IName -> TCEnv s Expr
judgeBind wip' bindINm = use thisMod >>= \modINm -> (wip' `MV.read` bindINm) >>= \case
  Left abs -> do
    freeTVars <- V.toList <$> use bruijnArgVars
    svwip     <- bindWIP <<.= (bindINm , False)
    svEscapes <- escapedVars <<%= (.|. intList2BitSet freeTVars)
    svLeaked  <- use leakedVars

    (tvarIdx , jb , ms , isRec) <- freshBiSubs 1 >>= \[idx] -> do
      MV.write wip' bindINm (Right $ Guard emptyBitSet idx)
      e <- use externs
      let required = emptyBitSet
      open  <- use openModules
      expr  <- infer e modINm open required (P._fnRhs abs)
      isRec <- snd <$> use bindWIP
      bindWIP .= svwip
      Right (Guard ms _tVar) <- MV.read wip' bindINm -- learn which binds had to be inferred as dependencies
      pure (idx , expr , ms , isRec)
    typeAnn <- getAnnotationType (P._fnSig abs)
    -- Mutuals check freeVars == 0 to see if can trim bis
    MV.write wip' bindINm (Right $ Mutual jb (intList2BitSet freeTVars) isRec tvarIdx typeAnn)

--  letBinds <- (.&. complement svLets) <$> use letBounds
--  (bitSet2IntList letBinds) `forM_` \l -> regeneralise l

    if setNBits (bindINm + 1) .&. ms /= 0 -- minimum (bindINm : ms) /= bindINm
      then pure jb
      else fromJust . head <$> generaliseBinds wip' svEscapes svLeaked (bindINm : bitSet2IntList ms) -- <* clearBiSubs 0

  Right b -> case b of
    BindOK _ _ _isRec e  -> pure e
    Mutual _e _freeVs _isRec tvar _tyAnn -> pure (Core (Var (VQBind $ mkQName modINm bindINm)) (TyVar tvar)) -- don't inline the expr

    Guard mutuals tvar -> fst <$> use bindWIP >>= \this ->
      ($> Core (Var (VQBind $ mkQName modINm bindINm)) (TyVar tvar)) $
      when (this /= bindINm) $ do
        MV.write wip' bindINm (Right $ Guard (mutuals `setBit` this) tvar)
        MV.modify wip' mF this where
          mF = \case
            Right (Guard ms tv) -> Right $ Guard (ms `setBit` bindINm) tv
            x -> abort (show x)
    b -> error (show b)

-- Converting user types to Types = Generalise to simplify and normalise the type
getAnnotationType ∷ Maybe P.TT -> TCEnv s (Maybe Type)
getAnnotationType ttAnn = case ttAnn of
  Nothing -> pure Nothing
  _ -> _
--Just t@P.Abs{} -> let
--  escapes = emptyBitSet
--  genGroundType t = case t of
--    TyGround{} -> generalise escapes (Right t)
--    t -> pure t -- may need to generalise under complex types
--  in fmap tyExpr $ infer t >>= \case
--  Core t ty -> Core t <$> genGroundType ty
--  Ty ty     -> Ty     <$> genGroundType ty
--  x         -> pure x
--Just t -> tyExpr <$> infer t -- no need to generalise if not Abs since no pi bounds

-- TODO This is slow and repeats work when regeneralisation is not necessary !
regeneralise :: MV.MVector s (Either P.FnDef Bind) -> Int -> TCEnv s ()
regeneralise wip' l = MV.read wip' l >>= \case
  Right (BindOK o _letbound r (Core t ty)) ->
    (Core t <$> generalise 0 (Right ty)) >>= MV.write wip' l . (\r t -> Right $ BindOK o False r t) r
  _ -> pure () -- <* traceM ("attempt to regeneralise non-let-bound: " <> show l)

generaliseBinds ∷ MV.MVector s (Either P.FnDef Bind) -> BitSet -> BitSet -> [Int] -> TCEnv s [Expr]
generaliseBinds wip' svEscapes svLeaked ms = ms `forM` \m -> MV.read wip' m >>= \case
 Left e -> error $ show e
 Right b -> case b of
  BindOK _ _ _r e -> pure e -- already handled mutual
  -- ! The order in which mutuals are generalise these is relevant
  Mutual naiveExpr freeVs isRec recTVar annotation -> do
    (_ars , inferred) <- case naiveExpr of
      Core expr coreTy -> (\(ars , ty) -> (ars , Core expr ty)) <$> do -- generalise the type
        (args , ty , free) <- case expr of
--        Abs (Lam ars free _fnTy , _t) -> pure (ars , coreTy , free) -- ? TODO why not free .|. freeVs
          _                             -> pure ([] , coreTy , freeVs)
        -- rec | mutual: if this bind : τ was used within itself then something bisubed with -τ
        _cast <- use bis >>= \v -> MV.read v recTVar <&> _mSub >>= \case
          TyGround [] -> BiEQ <$ MV.write v recTVar (BiSub ty (TyGround [])) -- not recursive / mutual
          _t          -> bisub ty (TyVar recTVar) -- ! recursive | mutual ⇒ bisub with -τ (itself)
        escaped <- use escapedVars
        g       <- generalise escaped (Left recTVar)
--      when global_debug $ use bis >>= \b -> use blen >>= \bl ->
--        [0 .. bl -1] `forM_` \i -> MV.read b i >>= \e -> traceM (show i <> " = " <> show e)
        when (free == 0 && null (drop 1 ms)) (clearBiSubs recTVar) -- ie. no mutuals and no escaped vars 
        pure (intList2BitSet (fst <$> args) , g)
      Ty t -> pure $ (emptyBitSet,) $ Ty $ if not isRec then t else case t of
        -- v should µbinder be inside the pi type ?
        TyPi (Pi ars t)   -> TyPi (Pi ars (TyGround [THMu 0 t]))
        TySi (Pi ars t) e -> TySi (Pi ars (TyGround [THMu 0 t])) e
        t -> TyGround [THMu 0 t]
      t -> pure (emptyBitSet , t)

    l <- leakedVars  <<.= svLeaked
    escapedVars .= svEscapes
    deadVars %= (.|. (l .&. complement svEscapes))

    done <- case (annotation , inferred) of -- Only Core type annotations are worth replacing inferred ones
      (Just ann , Core e inferredTy) -> Core e <$> checkAnnotation ann inferredTy
      _                              -> pure inferred
    MV.write wip' m (Right $ BindOK 0 False isRec done) -- todo letbound?
--  unless (null (drop 1 ms)) (regeneralise False `mapM_` ms) -- necessary eg. splitAt where let-bindings access this bind
--  if e == 0 then MV.write wip' m (BindOK 0 isRec done) else (letBounds %= (`setBit` m)) *> MV.write wip' m (LetBound isRec done)
--  when (ars .&. l /= 0) (regeneralise m *> traceM "regen")
    pure done
  b -> error (show b)

-- Prefer user's type annotation (it probably contains type aliases) over the inferred one
-- ! we may have inferred some missing information in type holes
checkAnnotation ∷ Type -> Type -> TCEnv s Type
checkAnnotation annTy inferredTy = do
  exts      <- use externs
--unaliased <- normaliseType mempty annTy
  check exts inferredTy annTy >>= \ok -> if ok
  then pure annTy
  else inferredTy <$ (errors . checkFails %= (CheckError inferredTy annTy:))
 
infer :: Externs -> ModuleIName -> Scope.OpenModules -> Scope.RequiredModules -> P.TT -> TCEnv s Expr
infer e modINm open required tt = let
  scopeparams = initParams open required
  in cata inferF (cata (solveScopesF e modINm) tt scopeparams) -- TODO master recursive composition
--in h tt scopeparams where
--  h = g . (solveScopesF e modINm) . fmap h . project
--  g = inferF . fmap g . project
--  h :: P.TT -> Params -> P.TTF (TCEnv s Expr) -> TCEnv s Expr
--  h = inferF . project . fmap (solveScopesF e modINm) . fmap h . project

inferF :: P.TTF (TCEnv s Expr) -> TCEnv s Expr
inferF = let
 withBruijnArgTVars :: Int -> TCEnv s a -> TCEnv s ([Type] , a)
 withBruijnArgTVars n go = freshBiSubs n >>= \argTVars -> do
   w <- (\v -> MV.unsafeGrowFront v n) =<< V.unsafeThaw =<< use bruijnArgVars
   imapM_ (\i n -> MV.write w i n) argTVars

   (bruijnArgVars .=) =<< V.unsafeFreeze w
   (map TyVar argTVars , ) <$> go <* (bruijnArgVars %= V.drop n)

  -- App is the only place typechecking can fail
 biUnifyApp fTy argTys = freshBiSubs 1 >>= \[retV] ->
   (, TyVar retV) <$> bisub fTy (prependArrowArgsTy argTys (TyVar retV))

 retCast rc tt = case rc of { BiEQ -> tt ; c -> case tt of { Core f ty -> Core (Cast c f) ty ; x -> error (show x) } }

 checkFails srcOff x = use tmpFails >>= \case
   [] -> pure x
   x  -> PoisonExpr <$ (tmpFails .= []) <* (errors . biFails %= (map (BiSubError srcOff) x ++))

 inferApp srcOff f args = let
   castRet ∷ BiCast -> ([Term] -> BiCast -> [Term]) -> Expr -> Expr
   castRet biret castArgs = \case
     Core (App f args) retTy -> case biret of
       CastApp _ac (Just pap) rc -> -- partial application TODO use argcasts
         retCast rc (Core (App (Instr (MkPAp (length pap))) (f : castArgs args biret)) retTy)
       CastApp _ac Nothing    rc -> retCast rc (Core (App f (castArgs args biret)) retTy)
       _ -> Core (App f args) retTy
     t -> t
   -- TODO This will let slip some bieq casts on function arguments
   castArg (a ∷ Term) = \case { BiEQ -> a ; CastApp [BiEQ] Nothing BiEQ -> a ; cast -> Cast cast a }
   castArgs args' cast = case cast of
     CastApp ac _maybePap _rc -> zipWith castArg args' (ac ++ repeat BiEQ)
     BiEQ -> args'
     _    -> _

-- checkRec e@(Core (App (Var (VQBind q)) args) t) = use thisMod >>= \mod -> use bindWIP <&> \b ->
--   if modName q == mod && unQName q == fst b && snd b then Core (RecApp (Var (VQBind q)) args) t else e
   checkRec e = pure e

   in if any isPoisonExpr (f : args) then pure PoisonExpr else do
     (biret , retTy) <- biUnifyApp (tyOfExpr f) (tyOfExpr <$> args)
     use tmpFails >>= \case
       [] -> castRet biret castArgs <$> (ttApp retTy (\i -> judgeBind _wip' i) f args >>= checkRec)
       x  -> PoisonExpr <$ -- trace ("problem fn: " <> show f ∷ Text)
         ((tmpFails .= []) *> (errors . biFails %= (map (\biErr -> BiSubError srcOff biErr) x ++)))

 judgeLabel qNameL exprs = let
   labTy = TyGround [THTyCon $ THTuple $ V.fromList $ tyOfExpr <$> exprs]
   es = exprs <&> \case
     Core t _ty -> t
     PoisonExpr -> Question
     x          -> error (show x)
   in Core (Label qNameL es) (TyGround [THTyCon $ THSumTy $ BSM.singleton (qName2Key qNameL) labTy])

 getQBind q = {-traceShow q $-} use thisMod >>= \m -> if modName q == m
   then use letBinds >>= \lvl -> MV.read lvl 0 >>= \bs -> -- binds at this module are at let-nest 0
     judgeBind bs (unQName q) <&> \case
       Core _t ty -> Core (Var $ VLetBind q) ty -- don't inline at this stage
       x         -> did_ x
   else use openModules >>= \openMods -> use externs >>= \exts ->
     case readQParseExtern openMods m exts (modName q) (unQName q) of
       Imported e -> pure e
       x -> error $ show x

 inferBlock :: P.Block -> Maybe (TCEnv s Expr) -> TCEnv s (Expr , V.Vector (LetMeta , Bind))
 inferBlock (P.Block _open _letType letBindings) go = do
   nest <- letNest <<%= (1+)
   block <- use letBinds >>= \lvl -> V.thaw (Left <$> letBindings) >>= \block -> block <$ MV.write lvl nest block
-- judgeBind block `mapM_` [0 .. V.length letBindings - 1]
-- r <- fromMaybe (pure PoisonExpr) go
   -- ! This won't typecheck unused let-binds in the let-in
   r <- maybe (PoisonExpr <$ judgeBind block `mapM_` [0 .. V.length letBindings - 1]) identity go

-- regeneralise block `mapM_` [0 .. V.length letBindings - 1]

   lets <- use letBinds >>= \lvl -> MV.read lvl nest >>= {-fmap did_ .-} V.unsafeFreeze
     <&> map ((\unused -> BindOK 0 True False $ PoisonExprWhy ("unused let-bound: " <> show unused)) ||| identity)
   letNest %= (\x -> x -1)
   pure (r , V.zipWith (\fn e -> (LetMeta (fn ^. P.fnNm) (-1) , e)) letBindings lets)

 in \case
  P.QuestionF -> pure $ Core Question tyBot
  P.WildCardF -> pure $ Core Question tyBot
  P.LetInF b Nothing -> inferBlock b Nothing <&> \(_ , lets) -> Core (LetBlock lets) tyBot
  P.LetInF b pInTT -> inferBlock b pInTT <&> \(inTT , lets) -> case inTT of
    Core t ty -> Core (LetBinds lets t) ty -- <* (fst <$> ls) `forM_` regeneralise True
    x -> x
  P.VarF v -> case v of -- vars : lookup in appropriate environment
    P.VBruijn b  -> use bruijnArgVars <&> \argTVars -> Core (VBruijn b) (TyVar $ argTVars V.! b)
    P.VExtern e  -> error $ "Unresolved VExtern: " <> show e
    P.VQBind q   -> getQBind q
    P.VLetBind q -> use letBinds >>= \lvl -> MV.read lvl (modName q) >>= \bs ->
      judgeBind bs (unQName q) <&> \case
        Core _t ty -> Core (Var $ VLetBind q) ty
        x          -> did_ x

  P.ForeignF _isVA i tt -> tt <&> \tExpr ->
    maybe (PoisonExprWhy ("not a type: " <> show tExpr)) (Core (Var (VForeign i))) (tyExpr tExpr)

  P.BruijnLamF (P.BruijnAbsF argCount argMetas _nest rhs) -> do
    let freeVars = emptyBitSet
    (argTVars , r) <- withBruijnArgTVars argCount rhs
    pure $ case r of
      Core term retTy -> if argCount == 0 then Core term retTy else
        let fnTy = prependArrowArgsTy argTVars retTy
            alignArgs :: These (IName, Int) Type -> (Int, Type)
            alignArgs = these ((,tyBot) . fst) ((-1,)) (\(i , _) b -> (i , b)) -- TODO argMetas should match argCount
        in  Core (BruijnAbsTyped argCount freeVars term (alignWith alignArgs argMetas argTVars) retTy) fnTy
--    Ty retTy -> Ty $ if argCount == 0 then retTy else TyPi (Pi (zip _args argTVars) retTy)
      t -> t

  P.AppF fTT argsTT -> fTT >>= \f -> sequence argsTT >>= inferApp (-1) f
  P.PExprAppF _prec q argsTT -> getQBind q >>= \f -> sequence argsTT >>= inferApp (-1) f
  P.RawExprF t -> t
  P.MixfixPoisonF t -> PoisonExpr <$ (tmpFails .= []) <* error (show t) -- (errors . scopeFails %= (e:))
  P.QVarF q -> getQBind q
--VoidExpr (QVar QName) (PExprApp p q tts) (MFExpr Mixfixy)

  P.TupleF _ts -> d_ "inference of tuple" (pure PoisonExpr)
  P.ProdF construct -> use externs >>= \ext -> do
    let (fieldsLocal , rawTTs) = unzip construct
        fields = qName2Key . readField ext <$> fieldsLocal
    exprs <- sequence rawTTs
    let (tts , tys) = unzip $ (\case { Core t ty -> (t , ty) ; x -> error $ show x }) <$> exprs
        mkFieldCol = \a b -> TyGround [THFieldCollision a b]
        retTycon = THProduct (BSM.fromListWith mkFieldCol $ zip fields tys)
    pure $ if isPoisonExpr `any` exprs
      then PoisonExpr
      else Core (Prod (BSM.fromList $ zip fields tts)) (TyGround [THTyCon retTycon])

  P.TTLensF o tt fieldsLocal maybeSet -> use externs >>= \ext -> tt >>= \record -> let
      fields = readField ext <$> fieldsLocal
      recordTy = tyOfExpr record
      mkExpected ∷ Type -> Type
      mkExpected dest = foldr (\fName ty -> TyGround [THTyCon $ THProduct (BSM.singleton (qName2Key fName) ty)]) dest fields
    in (>>= checkFails o) $ case record of
    (Core object objTy) -> case maybeSet of
      P.LensGet    -> freshBiSubs 1 >>= \[i] -> bisub recordTy (mkExpected (TyVar i))
        <&> \cast -> Core (TTLens (Cast cast object) fields LensGet) (TyVar i)

      -- LeafTy -> Record -> Record & { path : LeafTy }
      -- + is right for mergeTypes since this is output
      P.LensSet x  -> x <&> \case
--      new@(Core _newLeaf newLeafTy) -> Core (TTLens f fields (LensSet new)) (mergeTypes True objTy (mkExpected newLeafTy))
        leaf@(Core _newLeaf newLeafTy) ->  -- freshBiSubs 1 >>= \[i] -> bisub recordTy (mkExpected TyVar i)
          Core (TTLens object fields (LensSet leaf)) (mergeTypes True objTy (mkExpected newLeafTy))
        _ -> PoisonExpr

      P.LensOver x -> x >>= \fn -> do
         (ac , rc , outT , rT) <- freshBiSubs 3 >>= \[inI , outI , rI] -> let
           inT = TyVar inI ; outT = TyVar outI
           in do -- need 3 fresh TVars since we cannot assume anything about the "fn" or the "record"
           argCast <- bisub (tyOfExpr fn) (TyGround [THTyCon $ THArrow [inT] outT]) <&> \case
             CastApp [argCast] _pap BiEQ  -> argCast -- pap ?
             BiEQ                         -> BiEQ
             x -> error (show x)
           -- note. the typesystem does not atm support quantifying over field presences
           rCast <- bisub recordTy (mergeTVar rI (mkExpected inT))
           pure (argCast , rCast , outT , rI)

         let lensOverCast = case rc of
               CastProduct _drops [(asmIdx , _cast)] -> Cast (CastOver asmIdx ac fn outT) object
               BiEQ -> object
               _ -> error $ "expected CastProduct: " <> show rc

         pure $ Core lensOverCast (mergeTVar rT (mkExpected outT))

    PoisonExpr -> pure PoisonExpr
    t -> error $ "record type must be a term: " <> show t

  P.LabelF localL tts -> use externs >>= \ext -> sequence tts <&> judgeLabel (readLabel ext localL)

  -- Sumtype declaration
  P.GadtF alts -> use externs >>= \ext -> do
    let getTy = fromMaybe (TyGround [THPoison]) . tyExpr
        mkLabelCol a b = TyGround [THLabelCollision a b]
    sumArgsMap <- alts `forM` \(l , tyParams , _gadtSig@Nothing) -> do
      params <- tyParams `forM` \t -> getTy <$> t
      pure (qName2Key (readLabel ext l) , TyGround [THTyCon $ THTuple $ V.fromList params])
    pure $ Ty $ TyGround [THTyCon $ THSumTy $ BSM.fromListWith mkLabelCol sumArgsMap]

  P.MatchBF pscrut caseSplits catchAll -> use externs >>= \ext -> pscrut >>= \case 
    PoisonExpr -> pure PoisonExpr
    Core scrut gotScrutTy -> do
      let convAbs :: Expr -> (Term , Type)
          convAbs (Core t ty) = (t , ty)
          convAbs (PoisonExprWhy why) = (Poison why , tyBot)
          convAbs (PoisonExpr) = (Poison "" , tyBot)
          convAbs x = error (show x)
      (ls , elems) <- sequenceA caseSplits <&> unzip . BSM.toList . fmap convAbs
      -- Note we can't use the retTy of fn types in branchFnTys in case the alt returns a function
      let (alts , _branchFnTys) = unzip elems :: ([Term] , [Type])
          labels = qName2Key . readLabel ext <$> ls
          branchTys = elems <&> \case
            (BruijnAbsTyped _ _ _ _ retTy , _) -> retTy
            (_ , ty) -> ty
      def       <- sequenceA catchAll <&> fmap convAbs
      let retTy    = mergeTypeList False $ maybe branchTys ((: branchTys) . snd) def -- ? TODO why negative merge
          altTys   = alts <&> \case
            BruijnAbsTyped _ _ _t ars _retTy -> TyGround [THTyCon $ THTuple (V.fromList $ snd <$> ars)]
            _x -> TyGround [THTyCon $ THTuple mempty]
          scrutSum = BSM.fromList (zip labels altTys)
          scrutTy  = TyGround [THTyCon $ case def of
            Nothing          -> THSumTy scrutSum
            Just (_ , defTy) -> THSumOpen scrutSum defTy]
          matchTy = TyGround (mkTyArrow [scrutTy] retTy)
      (BiEQ , retT) <- biUnifyApp matchTy [gotScrutTy]
      pure $ Core (CaseB scrut retT (BSM.fromList (zip labels alts)) (fst <$> def)) retT
    x -> error $ show x

  P.InlineExprF e -> pure e
  P.LitF l           -> pure $ Core (Lit l) (TyGround [typeOfLit l])
  P.ScopePoisonF e   -> PoisonExpr <$ (tmpFails .= []) <* (errors . scopeFails %= (e:))
  P.DesugarPoisonF t -> pure $ Core (Poison t) tyBot
  P.ScopeWarnF w t   -> trace w t
  x -> error $ "not implemented: inference of: " <> show (embed $ P.Question <$ x)
