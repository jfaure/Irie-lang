-- : see "Algebraic subtyping" by Stephen Dolan https://www.cs.tufts.edu/~nr/cs257/archive/stephen-dolan/thesis.pdf
module Infer (judgeModule) where
import Prim ( PrimInstr(MkPAp) )
import BiUnify ( bisub )
import qualified ParseSyntax as P
import CoreSyn as C
import PrettyCore
import CoreUtils ( isPoisonExpr, mergeTVar, mergeTypeList, mergeTypes, mkTyArrow, prependArrowArgsTy, tyExpr, tyOfExpr )
import TTCalculus ( ttApp )
import Scope
import Errors
import TypeCheck ( check )
import TCState
import Externs ( typeOfLit, readField, readLabel, readParseExtern, readQParseExtern , Externs )
import Generalise ( generalise )

import Control.Lens
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV ( MVector, modify, new, read, replicate, write )
import qualified Data.Vector.Generic.Mutable as MV (unsafeGrowFront)
import qualified BitSetMap as BSM ( toList, fromList, fromListWith, singleton )
import Data.Functor.Foldable

judgeModule ∷ Int -> P.Module -> BitSet -> ModuleIName -> p -> V.Vector HName -> Externs.Externs -> p1 -> (JudgedModule , Errors)
judgeModule nBinds pm importedModules modIName _nArgs hNames exts _source = let
  modName   = pm ^. P.moduleName
  nArgs     = 0 -- pm ^. P.parseDetails . P.nArgs
  pBinds'   = V.fromListN nBinds (pm ^. P.bindings)
  in runST $ do
    wip'      <- MV.replicate nBinds Queued
    bis'      <- MV.new 64
    argVars'  <- MV.new nArgs
    c         <- MV.new 0
    st <- execStateT (judgeBind pBinds' wip' `mapM_` [0 .. nBinds-1]) $ TCEnvState
      { _pBinds   = pBinds'
      , _externs  = exts
      , _thisMod  = modIName

      , _wip      = wip'
      , _errors   = emptyErrors
      , _letBounds= emptyBitSet
      , _bruijnArgVars = mempty

      , _openModules = importedModules
      , _argVars  = argVars'
      , _bindWIP  = (0 , False)
      , _tmpFails = []
      , _blen     = 0
      , _bis      = bis'
      , _escapedVars  = emptyBitSet
      , _leakedVars   = emptyBitSet
      , _deadVars     = emptyBitSet
      , _bindsInScope = setNBits nBinds -- !! todo topbinds
      , _recVars      = emptyBitSet
      , _coOccurs     = c
      }
    wip'' <- V.unsafeFreeze (st ^. wip)
    pure (JudgedModule modIName modName nArgs hNames (pm ^. P.parseDetails . P.fields) (pm ^. P.parseDetails . P.labels) wip'' Nothing , st ^. errors) --TCErrors (st ^. scopeFails) (st ^. biFails) (st ^. checkFails))

-- uninline expr and insert qualified binding
judgeLocalBind b = use thisMod >>= \modINm -> use wip >>= \wip' -> use pBinds >>= \binds -> judgeBind binds wip' b <&> \case
  Core _ ty -> Core (Var $ VQBind (mkQName modINm b)) ty -- no need to inline the body yet
  t -> t

-- infer ≫ generalise ≫ check annotation
-- This stacks inference of forward references + let-binds and handles mutuals (only generalise at end of mutual block)
-- This includes noting leaked and escaped typevars
judgeBind ∷ V.Vector P.FnDef -> MV.MVector s Bind -> IName -> TCEnv s Expr
judgeBind ttBinds wip' bindINm = use thisMod >>= \modINm -> (wip' `MV.read` bindINm) >>= \case
  BindOK _ _ _isRec e  -> pure e
  Mutual _e _freeVs _isRec tvar _tyAnn -> pure (Core (Var (VQBind $ mkQName modINm bindINm)) (TyVar tvar)) -- don't inline the expr

  Guard mutuals tvar -> do
    this <- fst <$> use bindWIP
    when (this /= bindINm) $ do
      MV.write wip' bindINm (Guard (mutuals `setBit` this) tvar)
      MV.modify wip' (\(Guard ms tv) -> Guard (ms `setBit` bindINm) tv) this
    pure $ Core (Var (VQBind $ mkQName modINm bindINm)) (TyVar tvar)

  LetBound -> pure (Core (Var $ VQBind (mkQName modINm bindINm)) tyBot)
  Queued -> use wip >>= \wip' -> let
    abs      = ttBinds V.! bindINm
    freeVars = 0
    in do
--  in if P.fnRecType abs == P.Let then PoisonExpr <$ MV.write wip' bindINm LetBound else do -- HACK
    svwip     <- bindWIP <<.= (bindINm , False)
    freeTVars <- use argVars >>= \avs -> bitSet2IntList freeVars `forM` \i -> MV.read avs i
    svEscapes <- escapedVars <<%= (.|. intList2BitSet freeTVars)
    svLeaked  <- use leakedVars

    (tvarIdx , jb , ms , isRec) <- freshBiSubs 1 >>= \[idx] -> do
      MV.write wip' bindINm (Guard emptyBitSet idx)
      e <- use externs
      let required = emptyBitSet
      open  <- use openModules
--    expr  <- infer $ solveScopes e modINm open required (P.BruijnLam (P.fnMatches abs))
      expr  <- infer e modINm open required (P.fnMatches abs)
      isRec <- snd <$> use bindWIP
      bindWIP .= svwip
      Guard ms _tVar <- MV.read wip' bindINm -- learn which binds had to be inferred as dependencies
      pure (idx , expr , ms , isRec)
    typeAnn <- getAnnotationType (P.fnSig abs)
    MV.write wip' bindINm (Mutual jb freeVars isRec tvarIdx typeAnn)

--  letBinds <- (.&. complement svLets) <$> use letBounds
--  (bitSet2IntList letBinds) `forM_` \l -> regeneralise l

    if setNBits (bindINm + 1) .&. ms /= 0 -- minimum (bindINm : ms) /= bindINm
      then pure jb
      else fromJust . head <$> generaliseBinds svEscapes svLeaked (bindINm : bitSet2IntList ms) -- <* clearBiSubs 0
  b -> error (show b)

-- Converting user types to Types = Generalise to simplify and normalise the type
getAnnotationType ∷ Maybe P.TT -> TCEnv s (Maybe Type)
getAnnotationType ttAnn = case ttAnn of
  Nothing -> pure Nothing
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

-- let-bindings may contain unresolved tvars
regeneralise ∷ Bool -> Int -> TCEnv s ()
regeneralise makeLet l = use wip >>= \wip' -> do -- regeneralise all let-bounds whose escaped vars are now resolved
  MV.read wip' l >>= \case -- escapes have been resolved, need to solve them in our partially generalised types
--  LetBound r (Core t ty) -> (Core t <$> generalise 0 (Right ty)) >>= MV.write wip' l . LetBound r
--  BindOK o r (Core t ty) -> (Core t <$> generalise 0 (Right ty)) >>= MV.write wip' l . (if makeLet then LetBound else BindOK o) r
    BindOK o _letbound r (Core t ty) ->
      (Core t <$> generalise 0 (Right ty)) >>= MV.write wip' l . (BindOK o makeLet) r
    _ -> pure () -- <* traceM ("attempt to regeneralise non-let-bound: " <> show l)
--  _ -> error "attempt to regenaralise non-let-bound"

generaliseBinds ∷ BitSet -> BitSet -> [Int] -> TCEnv s [Expr]
generaliseBinds svEscapes svLeaked ms = use wip >>= \wip' -> ms `forM` \m -> MV.read wip' m >>= \case
  -- ! The order in which mutuals are generalise these is relevant
  Mutual naiveExpr freeVs isRec recTVar annotation -> do
    (_ars , inferred) <- case naiveExpr of
      Core expr coreTy -> (\(ars , ty) -> (ars , Core expr ty)) <$> do -- generalise the type
        (args , ty , free) <- case expr of
          Abs (Lam ars free _fnTy , _t) -> pure (ars , coreTy , free) -- ? TODO why not free .|. freeVs
          _                           -> pure ([] , coreTy , freeVs)
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
    MV.write wip' m (BindOK 0 False isRec done) -- todo letbound?
    unless (null (drop 1 ms)) (regeneralise False `mapM_` ms) -- necessary eg. splitAt where let-bindings access this bind
--  if e == 0 then MV.write wip' m (BindOK 0 isRec done) else (letBounds %= (`setBit` m)) *> MV.write wip' m (LetBound isRec done)
--  when (ars .&. l /= 0) (regeneralise m *> traceM "regen")
    pure done
  BindOK _ _ _r e -> pure e -- already handled mutual
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
  in cata inferF (snd (cata (solveScopesF e modINm) tt scopeparams)) -- TODO master recursive composition

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
     wip'    <- use wip
     pBinds' <- use pBinds
     (biret , retTy) <- biUnifyApp (tyOfExpr f) (tyOfExpr <$> args)
     scopes <- use bindsInScope
     use tmpFails >>= \case
       [] -> castRet biret castArgs <$> (ttApp retTy (judgeBind pBinds' wip') f args >>= checkRec)
       x  -> PoisonExpr <$ -- trace ("problem fn: " <> show f ∷ Text)
         ((tmpFails .= []) *> (errors . biFails %= (map (\biErr -> BiSubError srcOff biErr) x ++)))

 judgeLabel qNameL exprs = let
   labTy = TyGround [THTyCon $ THTuple $ V.fromList $ tyOfExpr <$> exprs]
   es = exprs <&> \case
     Core t _ty -> t
     PoisonExpr -> Question
     x          -> error (show x)
   in Core (Label qNameL es) (TyGround [THTyCon $ THSumTy $ BSM.singleton (qName2Key qNameL) labTy])
 -- TODO rm this: it comes from PExprApp after mixfix solves
 getQBind q = use thisMod >>= \m -> if modName q == m then judgeLocalBind (unQName q)
   else use openModules >>= \openMods -> use externs >>= \exts ->
     case readQParseExtern openMods m exts (modName q) (unQName q) of
       Imported e -> pure e
       x -> error $ show x

 in \case
  P.LetBindsF ls tt -> do
    _letbounds <- traverse snd ls
    inTT <- tt
    inTT <$ (fst <$> ls) `forM_` regeneralise True
  P.WildCardF -> pure $ Core Question (TyGround [])
  P.VarF v -> case v of -- vars : lookup in appropriate environment
    P.VBruijn b -> use bruijnArgVars <&> \argTVars -> Core (VBruijn b) (TyVar $ argTVars V.! b)
    P.VExtern e -> error $ "Unresolved VExtern: " <> show e
    P.VQBind q  -> getQBind q

  P.ForeignF   i tt -> tt <&> \tExpr -> maybe (PoisonExprWhy ("not a type: " <> show tExpr)) (Core (Var (VForeign i))) (tyExpr tExpr)
  P.ForeignVAF i tt -> tt <&> \tExpr -> maybe (PoisonExprWhy ("not a type: " <> show tExpr)) (Core (Var (VForeign i))) (tyExpr tExpr)

  P.BruijnLamF (P.BruijnAbsF argCount argMetas nest rhs) -> do
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
            BruijnAbsTyped _ _ t ars retTy -> TyGround [THTyCon $ THTuple (V.fromList $ snd <$> ars)]
            x -> TyGround [THTyCon $ THTuple mempty]
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
