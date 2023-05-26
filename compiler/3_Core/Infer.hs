-- : see "Algebraic subtyping" by Stephen Dolan https://www.cs.tufts.edu/~nr/cs257/archive/stephen-dolan/thesis.pdf
module Infer (judgeModule) where
import Prim ( PrimInstr(MkPAp) )
import Builtins (typeOfLit)
import BiUnify
import qualified ParseSyntax as P
import CoreSyn as C
import CoreUtils
import TTCalculus ( ttApp )
import Scope
import Errors
import Externs
import TypeCheck ( check )
import TCState
import Generalise (generalise)
import Control.Lens
import Data.Functor.Foldable
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified BitSetMap as BSM ( toList, fromList, fromVec, fromListWith, singleton, unzip )

--addBind :: Expr -> P.FnDef -> Expr
--addBind jm newDef = jm

judgeModule :: P.Module -> BitSet -> ModuleIName -> Externs.Externs -> V.Vector LoadedMod -> (Expr , Errors)
judgeModule pm importedModules modIName exts loaded = let
  scopeParams = initParams importedModules emptyBitSet -- open required
  modTT       = P.LetIn (P.Block True P.Let (pm ^. P.bindings)) Nothing
--bindNms = P._fnIName <$> (pm ^. P.bindings)
--scopeParams = initParams importedModules emptyBitSet
--  & lets %~ (.|. intList2BitSet (V.toList bindNms))
--  & letMap %~ V.modify (\v -> bindNms `iforM_` \i e -> MV.write v e (mkQName 0 i))
--bindings    = apo (scopeApoF exts modIName) (modTT , scopeParams)
  inferTT :: P.TT -> TCEnv s Expr
  inferTT tt = hypo inferF (scopeApoF exts modIName) (tt , scopeParams)
--inferBindings = mapM (use P.fnRhs >>= inferTT) (pm ^. P.bindings)
  in runST $ do
  letBinds' <- MV.new 32
  bis'      <- MV.new 0xFFF
  g         <- MV.new 0
  (_2 %~ (^. errors)) <$> runStateT (inferTT modTT) TCEnvState
    { _externs  = exts
    , _loadedMs = loaded
    , _thisMod  = modIName

    , _letBinds = letBinds'
    , _letNest  = 0
    , _errors   = emptyErrors
    , _bruijnArgVars = mempty
    , _bindStack = []

    , _openModules = importedModules
    , _tmpFails = []
    , _blen     = 0
    , _bis      = bis'

    , _freeLimit = 0
    , _letCaptures = 0
    , _captureRenames = g
    }

-- infer >> generalise >> check annotation
-- This stacks inference of forward references and let-binds and identifies mutual recursion
judgeBind :: Int -> IName -> TCEnv s Expr
judgeBind letDepth bindINm = let
  inferParsed :: MV.MVector s (Either P.FnDef Bind) -> P.FnDef -> TCEnv s Expr
  inferParsed wip' abs = freshBiSubs 1 >>= \[tvarIdx] -> do -- [tvarIdx] <- freshBiSubs 1
    bindStack %= ((letDepth , bindINm) :)
    MV.write wip' bindINm (Right (Guard emptyBitSet tvarIdx))
    svlc  <- letCaptures <<.= 0
    argVars <- use bruijnArgVars
    atLen <- V.length <$> use bruijnArgVars -- all capturable vars (reference where the letCaptures are valid bruijns)
    (captureRenames .=) =<< MV.new atLen

    rawExpr <- cata inferF (P._fnRhs abs)

    bindStack %= drop 1
    lcVars <- letCaptures <<%= (.|. svlc)
    argTVs <- use captureRenames >>= \cr -> bitSet2IntList lcVars `forM` \l -> (argVars V.! l ,) <$> MV.read cr l

    let freeVarCopies = snd <$> argTVs -- [Int]
        lc = (atLen , lcVars)
        expr = if True || lcVars == 0 then rawExpr else
          rawExpr & \(Core t ty) -> Core t (prependArrowArgsTy (tyVar <$> freeVarCopies) ty)

    -- generalise
    MV.read wip' bindINm >>= \case -- learn which binds had to be inferred as dependencies
      Right b@BindOK{} -> pure (bind2Expr b)
      Right (Guard ms tVar) -> do
        when (tVar /= tvarIdx) (error $ show (tVar , tvarIdx))
--      typeAnn <- getAnnotationType (P._fnSig abs)

        -- level mutuality: let a = { f = b.g } ; b = { g = a.f }
        -- check if any prev binds mutual with this one at its level
        let refs = setNBits bindINm .&. ms
        hasMutual <- let isMut i = MV.read wip' i <&> \case { Right (Guard ms _) -> refs .&. ms /= 0 ; _ -> False }
          in anyM isMut (bitSet2IntList refs)
        if hasMutual
          then Core (Var (VQBind (mkQName letDepth bindINm))) (tyVar tVar)
           <$ MV.write wip' bindINm (Right (Mut expr ms lc tVar))
           <* bisub (exprType expr) (tyVar tVar) -- ! recursive => bisub with -τ (itself)
           <* when (not (null freeVarCopies)) (error "mutual free vars")
          -- can generalise once all mutuals & associated tvars are fully constrained
          else genExpr wip' expr freeVarCopies lc tVar
      b -> error $ "panic: " <> show b

  -- reference to inference stack (forward ref | recursive | mutual)
  preInferred :: MV.MVector s (Either P.FnDef Bind) -> Bind -> TCEnv s Expr
  preInferred wip bind = case bind of
    BindOK _ _f e  -> pure e -- don't inline the expr
    Mut e _ms lc tvar -> genExpr wip e [] lc tvar
    -- v Stacked bind means this was either Mutual | recursive (also weird recursive: r = { a = r })
    Guard mutuals tvar -> do
      -- mark as stacked on top of all binds at this lvl
      -- mark it as mutual with all bind at its level
      bStack <- use bindStack
      let mbs = intList2BitSet $ snd <$> filter ((letDepth == ) . fst) bStack
      Core (Var (VQBind (mkQName letDepth bindINm))) (tyVar tvar)
        <$ MV.write wip bindINm (Right $ Guard (mutuals .|. mbs) tvar)

  genExpr :: MV.MVector s (Either P.FnDef Bind) -> Expr -> [Int] -> (Int , BitSet) -> Int -> TCEnv s Expr
  genExpr wip' (Core t ty) freeVarCopies letCapture@(_,freeVars) tvarIdx = do
    gTy  <- do
      _cast <- use bis >>= \v -> (v `MV.read` tvarIdx) <&> _mSub >>= \case
        TyGround [] -> BiEQ <$ MV.write v tvarIdx (BiSub ty (TyGround []))
        _t -> bisub ty (tyVar tvarIdx) -- ! recursive => bisub with -τ (itself)
      let copyFreeVarsTy = prependArrowArgsTy (tyVar <$> freeVarCopies) (tyVar tvarIdx)
      use blen >>= \bl -> use bis >>= \bis' ->
        lift (generalise bl bis' copyFreeVarsTy)
      -- <* when (free == 0 && null (drop 1 ms)) (clearBiSubs recTVar) -- ie. no mutuals and no escaped vars
    let rawRetExpr = Core (if freeVars == 0 then t else BruijnAbs (popCount freeVars) t) gTy
    retExpr <- pure rawRetExpr -- explicitFreeVarApp freeVars rawRetExpr
           -- TODO Mark eraser args (ie. lazy VBruijn rename for simplifer)
    retExpr <$ MV.write wip' bindINm (Right (BindOK optInferred letCapture retExpr))

  in use letBinds >>= (`MV.read` letDepth) >>= \wip -> (wip `MV.read` bindINm) >>=
    (inferParsed wip ||| preInferred wip) -- >>= \r -> r <$ (use bindStack >>= \bs -> when (null bs) (clearBiSubs 0))

-- judgeBind then uninline and add captured variable arguments if necessary
getLetBind letDepth bindINm = do
  expr <- judgeBind letDepth bindINm <&> \(Core _t ty) ->
    Core (Var (VLetBind (mkQName letDepth bindINm))) ty -- don't inline at this stage
  use letBinds >>= (`MV.read` letDepth) >>= \wip -> (wip `MV.read` bindINm) >>= \case
    Right (b@BindOK{}) -> free b & \(_ld , lc) -> explicitFreeVarApp lc expr
      -- ld doesn't matter since we dont β-reduce
    _ -> pure expr -- TODO handle mutuals that capture vars ; ie. spawn mutumorphisms

explicitFreeVarApp :: BitSet -> Expr -> TCEnv s Expr
explicitFreeVarApp lc e@(Core t ty) = if lc == 0 then pure e else let
  bruijnArs = bitSet2IntList lc
  appFree = App t (VBruijn <$> bruijnArs)
  in do
  atvs <- use bruijnArgVars
  (_cast , appTy) <- biUnifyApp ty (tyVar . (atvs V.!) <$> bruijnArs)
  pure (Core appFree appTy)
  -- trace (prettyTermRaw t <> "\n" <> prettyTermRaw (exprTerm c) <> "\n" <> prettyTyRaw ty) c

-- Prefer user's type annotation (it probably contains type aliases) over the inferred one
-- ! we may have inferred some missing information in type holes
checkAnnotation :: Type -> Type -> TCEnv s Type
checkAnnotation annTy inferredTy =
--unaliased <- normaliseType mempty annTy
  check _exts inferredTy annTy >>= \ok -> if ok
  then pure annTy
  else inferredTy <$ (errors . checkFails %= (CheckError inferredTy annTy:))

-- App is the only place inference can fail (if an arg doesn't subtype its expected type)
biUnifyApp :: Type -> [Type] -> TCEnv s (BiCast , Type)
biUnifyApp fTy argTys = freshBiSubs 1 >>= \[retV] ->
  (, tyVar retV) <$> bisub fTy (prependArrowArgsTy argTys (tyVar retV))

inferF :: P.TTF (TCEnv s Expr) -> TCEnv s Expr
inferF = let
 withBruijnArgTVars :: Int -> TCEnv s a -> TCEnv s ([Type] , a)
 withBruijnArgTVars n go = freshBiSubs n >>= \argTVars -> do
   (bruijnArgVars %= (V.fromList argTVars <>))
   (reverse $ tyVar <$> argTVars , ) <$> go <* (bruijnArgVars %= V.drop n)

 retCast rc tt@(Core f ty) = case rc of { BiEQ -> tt ; c -> Core (Cast c f) ty }

 checkFails srcOff x = use tmpFails >>= \case
   [] -> pure x
   x  -> poisonExpr <$ (tmpFails .= []) <* (errors . biFails %= (map (BiSubError srcOff) x ++))

 inferApp srcOff f args = let
   castRet :: BiCast -> ([Term] -> BiCast -> [Term]) -> Expr -> Expr
   castRet biret castArgs = \case
     Core (App f args) retTy -> case biret of
       CastApp _ac (Just pap) rc -> -- partial application TODO use argcasts
         retCast rc (Core (App (Instr (MkPAp (length pap))) (f : castArgs args biret)) retTy)
       CastApp _ac Nothing    rc -> retCast rc (Core (App f (castArgs args biret)) retTy)
       _ -> Core (App f args) retTy
     t -> t
   -- TODO This will let slip some bieq casts on function arguments
   castArg (a :: Term) = \case { BiEQ -> a ; CastApp [BiEQ] Nothing BiEQ -> a ; cast -> Cast cast a }
   castArgs args' cast = case cast of
     CastApp ac _maybePap _rc -> zipWith castArg args' (ac ++ repeat BiEQ)
     BiEQ -> args'
     _    -> _

   in if any isPoisonExpr (f : args) then pure poisonExpr else do
     (biret , retTy) <- biUnifyApp (exprType f) (exprType <$> args)
     use tmpFails >>= \case
       [] -> castRet biret castArgs <$> ttApp retTy (\i -> _judgeBind _0 i) f args -- >>= checkRecApp
       x  -> poisonExpr <$ -- trace ("problem fn: " <> show f :: Text)
         ((tmpFails .= []) *> (errors . biFails %= (map (\biErr -> BiSubError srcOff biErr) x ++)))

 judgeLabel qNameL exprs = let
   labTy = TyGround [THTyCon $ THTuple $ V.fromList (exprType <$> exprs)]
   es = exprs <&> \(Core t _ty) -> t
   in Core (Label qNameL es) (TyGround [THTyCon $ THSumTy $ BSM.singleton (qName2Key qNameL) labTy])

 getQBind q = use thisMod >>= \m -> if modName q == m -- binds at this module are at let-nest 0
   then getLetBind 0 (unQName q)
   else use loadedMs <&> \ls -> readQName ls (modName q) (unQName q)
     & fromMaybe (error (showRawQName q)) 

 -- Setup new freeVars env within a letNest ; should surround this with an inc of letNest, but not the inExpr
 newFreeVarEnv :: forall s a. TCEnv s a -> TCEnv s a
 newFreeVarEnv go = do
   fl   <- use bruijnArgVars <&> V.length
   svFL <- freeLimit <<.= fl
   go <* do
     freeLimit .= svFL
     letCaptures %= (`shiftR` (fl - svFL)) -- reset relative to next enclosing let-nest

 withLetNest go = letNest <<%= (1+) >>= \nest -> go nest <* (letNest %= \x -> x - 1)

 inferBlock :: V.Vector P.FnDef -> Maybe (TCEnv s Expr) -> TCEnv s (Expr , V.Vector (LetMeta , Bind))
 inferBlock letBindings inExpr = withLetNest $ \nest -> do
   newFreeVarEnv $ do
     use letBinds >>= \lvl -> V.thaw (Left <$> letBindings) >>= MV.write lvl nest
     judgeBind nest `mapM_` [0 .. V.length letBindings - 1]

   ret <- fromMaybe (pure poisonExpr) inExpr
   lets <- use letBinds >>= \lvl -> MV.read lvl nest >>= V.unsafeFreeze
     <&> map (fromRight (error "impossible: uninferred TT")) -- mapM judgeBind solved all
   mI <- use thisMod
   pure (ret , V.zipWith (\fn e -> (LetMeta (fnINameToQName mI fn) (fn ^. P.fnNm) (-1) , e)) letBindings lets)

 fnINameToQName mI fnDef = case P._fnRecType fnDef of
   P.LetTuple -> mkQName 0 (P._fnIName fnDef)
   _ -> mkQName mI (P._fnIName fnDef)

 mkFieldCol a b = TyGround [THFieldCollision a b]

 in \case
  P.QuestionF -> pure $ Core Question tyBot
  P.WildCardF -> pure $ Core Question tyBot
  -- letin Nothing = module / record, need to type it
  P.LetInF (P.Block _ _ lets) Nothing -> -- use thisMod >>= \mI -> 
    inferBlock lets Nothing <&> \(_ , lets) -> let -- [(LetMeta , Bind)]
    nms = lets <&> qName2Key . letName . fst
    tys = lets <&> exprType . bind2Expr . snd
    -- letnames = qualified on let-nests + 
    blockTy = THProduct (BSM.fromListWith mkFieldCol $ V.toList $ V.zip nms tys) -- TODO get the correct INames
    in Core (LetBlock lets) (TyGround [THTyCon blockTy])
  P.LetInF (P.Block _ _ lets) pInTT -> inferBlock lets pInTT <&> \(Core t ty , lets) -> Core (LetBinds lets t) ty
  P.ProdF pFields -> let -- duplicate the field name to both terms and types
    mkCore (ts , tys) = Core (Prod ts) (TyGround [THTyCon (THProduct tys)])
    in fmap (mkCore . BSM.unzip . BSM.fromVec)
      $ pFields `forM` \(i , s) -> s <&> \(Core t ty) -> (i , (t , ty))

  P.VarF v -> case v of -- vars : lookup in appropriate environment
    P.VBruijn b -> do
      argTVars <- use bruijnArgVars
      fLimit <- use freeLimit
      let lvl = V.length argTVars
          diff = lvl - fLimit
          bruijnAtBind = b - diff -- Bruijn idx relative to enclosing let-binding, not current lvl
      tv <- if b >= diff -- if b is free, insertOrRetrieve its local tvar
        then (letCaptures <<%= (`setBit` bruijnAtBind)) >>= \oldLc -> use captureRenames >>= \cr -> 
          if testBit oldLc bruijnAtBind
          then MV.read cr bruijnAtBind
          else freshBiSubs 1 >>= \[t] -> t <$ MV.write cr bruijnAtBind t
        else pure (argTVars V.! b) -- local arg
      pure $ Core (VBruijn b) (tyVar tv)
    P.VLetBind q -> getLetBind (modName q) (unQName q)
    P.VExtern e  -> error $ "Unresolved VExtern: " <> show e
    P.VBruijnLevel l -> error $ "unresolve bruijnLevel: " <> show l

  P.ForeignF{} {- isVA i tt-} -> error "not ready for foreign"
--  tt <&> \(Core _ttExpr ty) -> Core (Var (VForeign i)) ty

  P.BruijnLamF (P.BruijnAbsF argCount argMetas _nest rhs) ->
    withBruijnArgTVars argCount rhs <&> \(argTVars , Core term retTy) -> if argCount == 0 then Core term retTy else
      let fnTy = prependArrowArgsTy argTVars retTy
          alignArgs :: These (IName, Int) Type -> (Int, Type)
          alignArgs = these ((,tyBot) . fst) ((-1,)) (\(i , _) b -> (i , b)) -- TODO argMetas should match argCount
      in  Core (BruijnAbsTyped argCount term (alignWith alignArgs argMetas argTVars) retTy) fnTy

  P.AppF fTT argsTT  -> fTT  >>= \f -> sequence argsTT >>= inferApp (-1) f
  P.PExprAppF _prec q argsTT -> getQBind q >>= \f -> sequence argsTT >>= inferApp (-1) f
  P.RawExprF t -> t
  P.MixfixPoisonF t -> poisonExpr <$ (tmpFails .= []) <* (errors . mixfixFails %= (t:))
  P.QVarF q -> getQBind q

  P.TupleIdxF f tt -> tt >>= \(Core tuple tupleTy) -> freshBiSubs 1 >>= \[i] -> let
    qN = f -- qName2Key (mkQName 0 f) -- (-1 - f))
    expectedTy = TyGround [THTyCon $ THProduct (BSM.singleton qN (tyVar i))]
    in bisub tupleTy expectedTy <&> \cast ->
      let obj = TTLens tuple [qN] LensGet in Core (case cast of { BiEQ -> obj ; cast -> Cast cast obj }) (tyVar i)
  P.TTLensF o tt fieldsLocal maybeSet -> tt >>= \record -> use thisMod >>= \iM -> let
    fields = fieldsLocal -- readField ext <$> fieldsLocal
    recordTy = exprType record
    mkExpected :: Type -> Type
    mkExpected dest = foldr (\f ty -> TyGround [THTyCon $ THProduct (BSM.singleton (qName2Key $ mkQName iM f) ty)]) dest fields
--  mkExpected dest = foldr (\f ty -> TyGround [THTyCon $ THProduct (BSM.singleton f ty)]) dest fields
    in checkFails o =<< case record of
    Core object objTy -> case maybeSet of
      P.LensGet    -> freshBiSubs 1 >>= \[i] -> bisub recordTy (mkExpected (tyVar i)) <&> \cast ->
        let obj = case cast of { BiEQ -> object ; cast -> Cast cast object }
        in Core (TTLens obj fields LensGet) (tyVar i)

      -- LeafTy -> Record -> Record & { path : LeafTy }  (+ for mergeTypes since this is output)
      P.LensSet x  -> x <&> \leaf@(Core _newLeaf newLeafTy) ->
        -- freshBiSubs 1 >>= \[i] -> bisub recordTy (mkExpected tyVar i)
        Core (TTLens object fields (LensSet leaf)) (mergeTypes True objTy (mkExpected newLeafTy))

      P.LensOver x -> x >>= \fn -> do
         (ac , rc , outT , rT) <- freshBiSubs 3 >>= \[inI , outI , rI] -> let
           inT = tyVar inI ; outT = tyVar outI
           in do -- need 3 fresh TVars since we cannot assume anything about the "fn" or the "record"
           argCast <- bisub (exprType fn) (TyGround [THTyCon $ THArrow [inT] outT]) <&> \case
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

  -- TODO when to force introduce local label vs check if imported
  P.LabelF localL tts -> use thisMod >>= \thisM -> sequence tts 
    <&> judgeLabel (mkQName thisM localL) -- (readLabel ext localL)
  P.QLabelF q -> {-sequence tts <&>-} pure (judgeLabel q [])
 -- sumTy = THSumTy (BSM.singleton (qName2Key q) (TyGround [THTyCon $ THTuple mempty]))

  -- Sumtype declaration
--P.GadtF alts -> use externs >>= \ext -> do
--  let getTy = fromMaybe (TyGround [THPoison]) . tyExpr
--      mkLabelCol a b = TyGround [THLabelCollision a b]
--  sumArgsMap <- alts `forM` \(l , tyParams , _gadtSig@Nothing) -> do
--    params <- tyParams `forM` \t -> getTy <$> t
--    pure (qName2Key (readLabel ext l) , TyGround [THTyCon $ THTuple $ V.fromList params])
--  pure $ Core (Ty (TyGround [THTyCon $ THSumTy $ BSM.fromListWith mkLabelCol sumArgsMap])) (TySet 0)

  P.MatchBF pscrut caseSplits catchAll -> pscrut >>= \(Core scrut gotScrutTy) -> do
    let convAbs :: Expr -> (Term , Type) = \(Core t ty) -> (t , ty)
    (labels , elems) <- sequenceA caseSplits <&> unzip . BSM.toList . fmap convAbs
    def <- sequenceA catchAll <&> fmap convAbs
    let (alts , _rawAltTs) = unzip elems
        branchTys = elems <&> \case
          (BruijnAbsTyped _ _ _ retTy , _) -> retTy -- alts are functions of their label params
          (_ , ty) -> ty
        retTy  = mergeTypeList False $ maybe branchTys ((: branchTys) . snd) def -- ? TODO why negative merge
        altTys = alts <&> \case
          BruijnAbsTyped _ _t ars _retTy -> TyGround [THTyCon $ THTuple (V.fromList $ snd <$> ars)]
          _x -> TyGround [THTyCon $ THTuple mempty]
        scrutSum = BSM.fromList (zip labels altTys)
        scrutTy  = TyGround [THTyCon $ if isJust def then THSumOpen scrutSum else THSumTy scrutSum]
        matchTy = TyGround (mkTyArrow [scrutTy] retTy)
    (b , retT) <- biUnifyApp matchTy [gotScrutTy]
    case b of { BiEQ -> pure () ; _ -> error "expected bieq" }
    pure $ Core (CaseB scrut retT (BSM.fromList (zip labels alts)) (fst <$> def)) retT

  P.InlineExprF e -> pure e
  P.LitF l           -> pure $ Core (Lit l) (TyGround [typeOfLit l])
  P.ScopePoisonF e   -> poisonExpr <$ (tmpFails .= []) <* (errors . scopeFails %= (e:))
  P.DesugarPoisonF t -> poisonExpr <$ (tmpFails .= []) <* (errors . unpatternFails %= (t:))
  P.ScopeWarnF w t   -> (errors . scopeWarnings %= (w:)) *> t
  x -> error $ "not implemented: inference of: " <> show (embed $ P.Question <$ x)
