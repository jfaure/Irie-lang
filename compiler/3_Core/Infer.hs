-- : see "Algebraic subtyping" by Stephen Dolan https://www.cs.tufts.edu/~nr/cs257/archive/stephen-dolan/thesis.pdf
-- * replace forward references (Externs) with their name and identify recursive and mutual bindings
module Infer (judgeModule) where
import Prim ( PrimInstr(MkPAp) )
import BiUnify ( bisub )
import qualified ParseSyntax as P
import CoreSyn as C
import CoreUtils ( isPoisonExpr, mergeTVar, mergeTypeList, mergeTypes, mkTyArrow, prependArrowArgsTy, tyExpr, tyOfExpr )
import TTCalculus ( ttApp )
import Errors
import TypeCheck ( check )
import TCState
import DesugarParse ( matches2TT, patterns2TT )
import Externs ( typeOfLit, readField, readLabel, readParseExtern, readQParseExtern )
import Mixfix ( solveMixfixes )
import Generalise ( generalise )

import Control.Lens ( (^.), use, (<<%=), (<<.=), (%=), (.=), Field2(_2) )
import Data.List ( unzip4, zipWith3 )
import qualified Data.Vector as V ( Vector, (!), fromList, fromListN, unsafeFreeze )
import qualified Data.Vector.Mutable as MV ( MVector, modify, new, read, replicate, write )
import qualified BitSetMap as BSM ( fromList, fromListWith, singleton )

judgeModule nBinds pm importedModules modIName _nArgs hNames exts _source = let
  modName   = pm ^. P.moduleName
  nArgs     = pm ^. P.parseDetails . P.nArgs
  modBinds' = pm ^. P.parseDetails . P.topBinds
  pBinds'   = V.fromListN nBinds (pm ^. P.bindings)
--nFields = M.size (pm ^. P.parseDetails . P.fields)
--nLabels = M.size (pm ^. P.parseDetails . P.labels)
--normFields = argSort nFields (pm ^. P.parseDetails . P.fields)
--normLabels = argSort nLabels (pm ^. P.parseDetails . P.labels)
--fromRevListN n l = V.create $ do
--  v ← MV.new n
--  v <$ zipWithM (\i e → MV.write v i e) [n-1,n-2..0] l
  in runST $ do
    wip'      ← MV.replicate nBinds Queued
    bis'      ← MV.new 64
    argVars'  ← MV.new nArgs
    c         ← MV.new 0
    st ← execStateT (judgeBind pBinds' wip' `mapM_` [0 .. nBinds-1]) $ TCEnvState
--  st ← execStateT (judgeBind `mapM_` [nBinds-1 , nBinds-2..0]) $ TCEnvState
      { _pBinds   = pBinds'
      , _externs  = exts
      , _thisMod  = modIName

      , _wip      = wip'
      , _errors   = emptyErrors
      , _letBounds= emptyBitSet

      , _openModules = importedModules
      , _argVars  = argVars'
      , _bindWIP  = (0 , False)
      , _tmpFails = []
      , _blen     = 0
      , _bis      = bis'
      , _escapedVars = emptyBitSet
      , _leakedVars  = emptyBitSet
      , _deadVars    = emptyBitSet
      , _bindsInScope= modBinds'

      , _recVars     = emptyBitSet
      , _coOccurs    = c
      }
    wip''    ← V.unsafeFreeze (st ^. wip)
    pure (JudgedModule modIName modName nArgs hNames (pm ^. P.parseDetails . P.fields) (pm ^. P.parseDetails . P.labels) wip''
          , st ^. errors) --TCErrors (st ^. scopeFails) (st ^. biFails) (st ^. checkFails))

-- uninline expr and insert qualified binding
judgeLocalBind b = use thisMod ≫= \modINm → use wip ≫= \wip' → use pBinds ≫= \binds → judgeBind binds wip' b <&> \case
  Core _ ty → Core (Var $ VQBind (mkQName modINm b)) ty -- no need to inline the body yet
  t → t

-- infer ≫ generalise ≫ check annotation
-- This stacks inference of forward references + let-binds and handles mutuals (only generalise at end of mutual block)
-- This includes noting leaked and escaped typevars
judgeBind ∷ V.Vector P.FnDef → MV.MVector s Bind → IName → TCEnv s Expr
judgeBind ttBinds wip' bindINm = use thisMod ≫= \modINm → (wip' `MV.read` bindINm) ≫= \case
  BindOK _ _ _isRec e  → pure e
  Mutual _e _freeVs _isRec tvar _tyAnn → pure (Core (Var (VQBind $ mkQName modINm bindINm)) (TyVar tvar)) -- don't inline the expr

  Guard mutuals tvar → do
    this ← fst <$> use bindWIP
    when (this /= bindINm) $ do
      MV.write wip' bindINm (Guard (mutuals `setBit` this) tvar)
      MV.modify wip' (\(Guard ms tv) → Guard (ms `setBit` bindINm) tv) this
    pure $ Core (Var (VQBind $ mkQName modINm bindINm)) (TyVar tvar)

  Queued → use wip ≫= \wip' → let
    abs      = ttBinds V.! bindINm
    freeVars = P.fnFreeVars abs
    in do
    svwip     ← bindWIP <<.= (bindINm , False)
    freeTVars ← use argVars ≫= \avs → bitSet2IntList freeVars `forM` \i → MV.read avs i
    svEscapes ← escapedVars <<%= (.|. intList2BitSet freeTVars)
    svLeaked  ← use leakedVars

    (tvarIdx , jb , ms , isRec) ← freshBiSubs 1 ≫= \[idx] → do
      MV.write wip' bindINm (Guard emptyBitSet idx)
      expr  ← infer (P.Abs abs)
      isRec ← snd <$> use bindWIP
      bindWIP .= svwip
      Guard ms _tVar ← MV.read wip' bindINm -- learn which binds had to be inferred as dependencies
      pure (idx , expr , ms , isRec)
    typeAnn ← getAnnotationType (P.fnSig abs)
    MV.write wip' bindINm (Mutual jb freeVars isRec tvarIdx typeAnn)

--  letBinds ← (.&. complement svLets) <$> use letBounds
--  (bitSet2IntList letBinds) `forM_` \l → regeneralise l

    if setNBits (bindINm + 1) .&. ms /= 0 -- minimum (bindINm : ms) /= bindINm
      then pure jb
      else fromJust . head <$> generaliseBinds svEscapes svLeaked (bindINm : bitSet2IntList ms) -- <* clearBiSubs 0
  b → error (show b)

-- Converting user types to Types = Generalise to simplify and normalise the type
getAnnotationType ∷ Maybe P.TT → TCEnv s (Maybe Type)
getAnnotationType ttAnn = case ttAnn of
  Nothing → pure Nothing
  Just t@P.Abs{} → let
    escapes = emptyBitSet
    genGroundType t = case t of
      TyGround{} → generalise escapes (Right t)
      t → pure t -- may need to generalise under complex types
    in fmap tyExpr $ infer t ≫= \case
    Core t ty → Core t <$> genGroundType ty
    Ty ty     → Ty     <$> genGroundType ty
    x         → pure x
  Just t → tyExpr <$> infer t -- no need to generalise if not Abs since no pi bounds

-- let-bindings may contain unresolved tvars
regeneralise ∷ Bool → Int → TCEnv s ()
regeneralise makeLet l = use wip ≫= \wip' → do -- regeneralise all let-bounds whose escaped vars are now resolved
  MV.read wip' l ≫= \case -- escapes have been resolved, need to solve them in our partially generalised types
--  LetBound r (Core t ty) → (Core t <$> generalise 0 (Right ty)) ≫= MV.write wip' l . LetBound r
--  BindOK o r (Core t ty) → (Core t <$> generalise 0 (Right ty)) ≫= MV.write wip' l . (if makeLet then LetBound else BindOK o) r
    BindOK o _letbound r (Core t ty) →
      (Core t <$> generalise 0 (Right ty)) ≫= MV.write wip' l . (BindOK o makeLet) r
    _ → pure () -- <* traceM ("attempt to regeneralise non-let-bound: " <> show l)
--  _ → error "attempt to regenaralise non-let-bound"

generaliseBinds ∷ BitSet → BitSet → [Int] → TCEnv s [Expr]
generaliseBinds svEscapes svLeaked ms = use wip ≫= \wip' → ms `forM` \m → MV.read wip' m ≫= \case
  -- ! The order in which mutuals are generalise these is relevant
  Mutual naiveExpr freeVs isRec recTVar annotation → do
    (_ars , inferred) ← case naiveExpr of
      Core expr coreTy → (\(ars , ty) → (ars , Core expr ty)) <$> do -- generalise the type
        (args , ty , free) ← case expr of
          Abs (Lam ars free _fnTy , _t) → pure (ars , coreTy , free) -- ? TODO why not free .|. freeVs
          _                           → pure ([] , coreTy , freeVs)
        -- rec | mutual: if this bind : τ was used within itself then something bisubed with -τ
        _cast ← use bis ≫= \v → MV.read v recTVar <&> _mSub ≫= \case
          TyGround [] → BiEQ <$ MV.write v recTVar (BiSub ty (TyGround [])) -- not recursive / mutual
          _t          → bisub ty (TyVar recTVar) -- ! recursive | mutual ⇒ bisub with -τ (itself)
        escaped ← use escapedVars
        g       ← generalise escaped (Left recTVar)
--      when global_debug $ use bis ≫= \b → use blen ≫= \bl →
--        [0 .. bl -1] `forM_` \i → MV.read b i ≫= \e → traceM (show i <> " = " <> show e)
        when (free == 0 && null (drop 1 ms)) (clearBiSubs recTVar) -- ie. no mutuals and no escaped vars 
        pure (intList2BitSet (fst <$> args) , g)
      Ty t → pure $ (emptyBitSet,) $ Ty $ if not isRec then t else case t of
        -- v should µbinder be inside the pi type ?
        TyPi (Pi ars t)   → TyPi (Pi ars (TyGround [THMu 0 t]))
        TySi (Pi ars t) e → TySi (Pi ars (TyGround [THMu 0 t])) e
        t → TyGround [THMu 0 t]
      t → pure (emptyBitSet , t)

    l ← leakedVars  <<.= svLeaked
    escapedVars .= svEscapes
    deadVars %= (.|. (l .&. complement svEscapes))

    done ← case (annotation , inferred) of -- Only Core type annotations are worth replacing inferred ones
      (Just ann , Core e inferredTy) → Core e <$> checkAnnotation ann inferredTy
      _                              → pure inferred
    MV.write wip' m (BindOK 0 False isRec done) -- todo letbound?
    unless (null (drop 1 ms)) (regeneralise False `mapM_` ms) -- necessary eg. splitAt where let-bindings access this bind
--  if e == 0 then MV.write wip' m (BindOK 0 isRec done) else (letBounds %= (`setBit` m)) *> MV.write wip' m (LetBound isRec done)
--  when (ars .&. l /= 0) (regeneralise m *> traceM "regen")
    pure done
  BindOK _ _ _r e → pure e -- already handled mutual
  b → error (show b)

-- Prefer user's type annotation (it probably contains type aliases) over the inferred one
-- ! we may have inferred some missing information in type holes
checkAnnotation ∷ Type → Type → TCEnv s Type
checkAnnotation annTy inferredTy = do
  exts      ← use externs
--unaliased ← normaliseType handleExtern mempty annTy
  check handleExtern exts inferredTy annTy ≫= \ok → if ok
  then pure annTy
  else inferredTy <$ (errors . checkFails %= (CheckError inferredTy annTy:))

 -- TODO don't allow `bind = lonemixfixword`
handleExtern = let mfwOK = True in \case
  ForwardRef b         → judgeLocalBind b -- was a forward reference not an extern
  Imported e           → pure e
  NotOpened m h        → PoisonExpr <$ (errors . scopeFails %= (ScopeNotImported h m:))
  NotInScope  h        → PoisonExpr <$ (errors . scopeFails %= (ScopeError h:))
  AmbiguousBinding h m → PoisonExpr <$ (errors . scopeFails %= (AmbigBind h m :))
  MixfixyVar m         → if mfwOK then pure (MFExpr m)
    else PoisonExpr <$ (errors . scopeFails %= (ScopeError "(mixfix word cannot be a binding)" :))
  x → error (show x)

infer ∷ P.TT → TCEnv s Expr
infer = let
 getArgTVars args = use argVars ≫= \argPerms → map TyVar
   <$> (freshBiSubs (length args) ≫= \argTVars → zipWithM (\a v → v <$ MV.write argPerms a v) args argTVars)

  -- App is the only place typechecking can fail
 biUnifyApp fTy argTys = freshBiSubs 1 ≫= \[retV] →
   (, TyVar retV) <$> bisub fTy (prependArrowArgsTy argTys (TyVar retV))

 retCast rc tt = case rc of { BiEQ → tt ; c → case tt of { Core f ty → Core (Cast c f) ty ; x → error (show x) } }

 checkFails srcOff x = use tmpFails ≫= \case
   [] → pure x
   x  → PoisonExpr <$ (tmpFails .= []) <* (errors . biFails %= (map (BiSubError srcOff) x ++))

 inferApp srcOff f args = let
   castRet ∷ BiCast → ([Term] → BiCast → [Term]) → Expr → Expr
   castRet biret castArgs = \case
     Core (App f args) retTy → case biret of
       CastApp _ac (Just pap) rc → -- partial application TODO use argcasts
         retCast rc (Core (App (Instr (MkPAp (length pap))) (f : castArgs args biret)) retTy)
       CastApp _ac Nothing    rc → retCast rc (Core (App f (castArgs args biret)) retTy)
       _ → Core (App f args) retTy
     t → t
   -- TODO This will let slip some bieq casts on function arguments
   castArg (a ∷ Term) = \case { BiEQ → a ; CastApp [BiEQ] Nothing BiEQ → a ; cast → Cast cast a }
   castArgs args' cast = case cast of
     CastApp ac _maybePap _rc → zipWith castArg args' (ac ++ repeat BiEQ)
     BiEQ → args'
     _    → _

-- checkRec e@(Core (App (Var (VQBind q)) args) t) = use thisMod ≫= \mod → use bindWIP <&> \b →
--   if modName q == mod && unQName q == fst b && snd b then Core (RecApp (Var (VQBind q)) args) t else e
   checkRec e = pure e

   in if any isPoisonExpr (f : args) then pure PoisonExpr else do
     wip' ← use wip
     pBinds' ← use pBinds
     (biret , retTy) ← biUnifyApp (tyOfExpr f) (tyOfExpr <$> args)
     use tmpFails ≫= \case
       [] → castRet biret castArgs <$> (ttApp retTy (judgeBind pBinds' wip') handleExtern f args ≫= checkRec)
       x  → PoisonExpr <$ -- trace ("problem fn: " <> show f ∷ Text)
         ((tmpFails .= []) *> (errors . biFails %= (map (\biErr → BiSubError srcOff biErr) x ++)))

 judgeLabel qNameL exprs = let
   labTy = TyGround [THTyCon $ THTuple $ V.fromList $ tyOfExpr <$> exprs]
   es = exprs <&> \case
     Core t _ty → t
     PoisonExpr → Question
     x          → error (show x)
   in Core (Label qNameL es) (TyGround [THTyCon $ THSumTy $ BSM.singleton (qName2Key qNameL) labTy])

 in \case
  P.LetBinds ls tt → do
    svScope ← bindsInScope <<%= (.|. ls)
    inTT ← infer tt
    bitSet2IntList ls `forM_` regeneralise True
    bindsInScope .= svScope
    pure inTT
  P.WildCard → pure $ Core Question (TyGround [])
  P.Var v → case v of -- vars : lookup in appropriate environment
    P.VLocal l     → use argVars ≫= (`MV.read` l) <&> \t → Core (Var (VArg l)) (TyVar t)
    P.VBind b      → use bindsInScope ≫= \scoped → if scoped `testBit` b
      then use bindWIP ≫= \(this , _) → when (this == b) (bindWIP . _2 .= True) *> judgeLocalBind b ≫= \case
        -- don't inline type aliases; we want to reuse them to improve error messages
        Ty{} → use thisMod <&> \mod → Ty (TyAlias (mkQName mod b))
        t    → pure t
      else PoisonExpr <$ (errors . scopeFails %= (ScopeLetBound b :))
    P.VExtern i    → use thisMod ≫= \mod → use externs ≫= \e → use openModules ≫= \open →
      handleExtern (readParseExtern open mod e i)
    _ → _

  P.Foreign i tt   → infer tt <&> \case
    PoisonExpr → PoisonExpr
    ty         → Core (Var (VForeign i)) (fromMaybe (error $ "not a type: " <> show ty) (tyExpr ty))
  P.ForeignVA i tt → infer tt <&> \case
    PoisonExpr → PoisonExpr
    ty         → Core (Var (VForeign i)) (fromMaybe (error $ "not a type: " <> show ty) (tyExpr ty))

  -- TODO shouldn't be tyAnn here if it is ignored
  P.Abs (P.FnDef _hNm _letRecT _mf freeVars matches _tyAnn) → let
    (argsAndTys , tt) = matches2TT matches
    (args , _argAnns)  = unzip argsAndTys
    in do
    argTVars ← getArgTVars args
    infer tt <&> \case
      Core x ty → case args of
        []  → Core x ty
        args → let fnTy = prependArrowArgsTy argTVars ty
          in Core (Abs (Lam (zip args argTVars) freeVars fnTy , x)) fnTy
      Ty retTy → Ty $ case args of
        []   → retTy
        args → TyPi (Pi (zip args argTVars) retTy)
      t → t

  P.App fTT argsTT → infer fTT ≫= \f → (infer `mapM` argsTT) ≫= inferApp (-1) f
  P.Juxt srcOff juxt → let
    inferExprApp srcOff = \case
      ExprApp _fE [] → panic "impossible: empty expr App"
      ExprApp fE argsE → inferExprApp srcOff fE ≫= \case
        Core (Label iLabel []) _ → (inferExprApp srcOff `mapM` argsE) <&> judgeLabel iLabel
        Core (Label _ ars) _ → error (show ars) -- TODO why are we ignoring label args
        f → (inferExprApp srcOff `mapM`  argsE) ≫= inferApp srcOff f
      QVar q → use thisMod ≫= \modIName → use externs ≫= \e → use openModules ≫= \open →
        handleExtern (readQParseExtern open modIName e (modName q) (unQName q))
      MFExpr{}   → PoisonExpr <$ (errors . scopeFails %= (AmbigBind "mixfix word" [] :))
      core → pure core
    -- if y then (letIn x else y) ⇒ need to extract [x else y] from sub-juxtstream
--  juxt' = concatMap (\case { P.LetBinds ls (P.Juxt o2 inE) → inE ; t → [t] }) juxt
    in solveMixfixes <$> (infer `mapM` juxt) ≫= inferExprApp srcOff

  P.Cons construct → use externs ≫= \ext → do
    let (fieldsLocal , rawTTs) = unzip construct
        fields = qName2Key . readField ext <$> fieldsLocal
    exprs ← infer `mapM` rawTTs
    let (tts , tys) = unzip $ (\case { Core t ty → (t , ty) ; x → error $ show x }) <$> exprs
        mkFieldCol = \a b → TyGround [THFieldCollision a b]
        retTycon = THProduct (BSM.fromListWith mkFieldCol $ zip fields tys)
    pure $ if isPoisonExpr `any` exprs
      then PoisonExpr
      else Core (Cons (BSM.fromList $ zip fields tts)) (TyGround [THTyCon retTycon])

  P.TTLens o tt fieldsLocal maybeSet → use externs ≫= \ext → infer tt ≫= \record → let
      fields = readField ext <$> fieldsLocal
      recordTy = tyOfExpr record
      mkExpected ∷ Type → Type
      mkExpected dest = foldr (\fName ty → TyGround [THTyCon $ THProduct (BSM.singleton (qName2Key fName) ty)]) dest fields
    in (≫= checkFails o) $ case record of
    (Core object objTy) → case maybeSet of
      P.LensGet    → freshBiSubs 1 ≫= \[i] → bisub recordTy (mkExpected (TyVar i))
        <&> \cast → Core (TTLens (Cast cast object) fields LensGet) (TyVar i)

      -- LeafTy → Record → Record & { path : LeafTy }
      -- + is right for mergeTypes since this is output
      P.LensSet x  → infer x <&> \case
--      new@(Core _newLeaf newLeafTy) → Core (TTLens f fields (LensSet new)) (mergeTypes True objTy (mkExpected newLeafTy))
        leaf@(Core _newLeaf newLeafTy) →  -- freshBiSubs 1 ≫= \[i] → bisub recordTy (mkExpected TyVar i)
          Core (TTLens object fields (LensSet leaf)) (mergeTypes True objTy (mkExpected newLeafTy))
        _ → PoisonExpr

      P.LensOver x → infer x ≫= \fn → do
         (ac , rc , outT , rT) ← freshBiSubs 3 ≫= \[inI , outI , rI] → let
           inT = TyVar inI ; outT = TyVar outI
           in do -- need 3 fresh TVars since we cannot assume anything about the "fn" or the "record"
           argCast ← bisub (tyOfExpr fn) (TyGround [THTyCon $ THArrow [inT] outT]) <&> \case
             CastApp [argCast] _pap BiEQ  → argCast -- pap ?
             BiEQ                         → BiEQ
             x → error (show x)
           -- note. the typesystem does not atm support quantifying over field presences
           rCast ← bisub recordTy (mergeTVar rI (mkExpected inT))
           pure (argCast , rCast , outT , rI)

         let lensOverCast = case rc of
               CastProduct _drops [(asmIdx , _cast)] → Cast (CastOver asmIdx ac fn outT) object
               BiEQ → object
               _ → error $ "expected CastProduct: " <> show rc

         pure $ Core lensOverCast (mergeTVar rT (mkExpected outT))

    PoisonExpr → pure PoisonExpr
    t → error $ "record type must be a term: " <> show t

  P.Label localL tts → use externs ≫= \ext → (infer `mapM` tts) <&> judgeLabel (readLabel ext localL)

  -- Sumtype declaration
  P.Gadt alts → use externs ≫= \ext → do
    let getTy = fromMaybe (TyGround [THPoison]) . tyExpr
        mkLabelCol a b = TyGround [THLabelCollision a b]
    sumArgsMap ← alts `forM` \(l , tyParams , _gadtSig@Nothing) → do
      params ← tyParams `forM` \t → getTy <$> infer t
      pure (qName2Key (readLabel ext l) , TyGround [THTyCon $ THTuple $ V.fromList params])
    pure $ Ty $ TyGround [THTyCon $ THSumTy $ BSM.fromListWith mkLabelCol sumArgsMap]

  P.Match alts catchAll → use externs ≫= \ext → let
    -- * desugar all patterns in the alt fns (whose args are parameters of the label)
    -- * ret type is a join of all the labels
    desugarFns = \(lname , _free , pats , tt) → let
      (argsAndTys , e) = patterns2TT pats tt
      (args , _argAnns) = unzip argsAndTys
      in (qName2Key (readLabel ext lname) , args , _ , e)
    (labels , args , _ , exprs) = unzip4 $ (desugarFns <$> alts)
    in do
    argTVars ← getArgTVars `mapM` args
    alts ← infer `mapM` exprs
    def  ← sequenceA (infer <$> catchAll)
    let retTys  = tyOfExpr <$> (maybeToList def ++ alts)
        retTy   = mergeTypeList False retTys -- ? TODO why is this a negative merge

        altTys  = map (\argTVars → TyGround [THTyCon $ THTuple (V.fromList argTVars)]) argTVars
        scrutSum = BSM.fromList (zip labels altTys)
--      scrutSumD = maybe scrutSum (\d → (qName2Key (mkQName 0 0) , tyOfExpr d) : scrutSum) def
        scrutTy = case def of
          Nothing → TyGround [THTyCon $ THSumTy scrutSum]
          Just t  → TyGround [THTyCon $ THSumOpen scrutSum (tyOfExpr t)]
        matchTy = TyGround $ mkTyArrow [scrutTy] retTy
        argAndTys  = zipWith zip args argTVars
        altsMap = let
          addAbs ty (Core t _) args = (Lam args 0 ty , t)
--        addAbs _ty PoisonExpr _ = Lam [] 0 Poison tyBot
          addAbs _ty e _ = error (show e)
          in BSM.fromList $ zip labels (zipWith3 addAbs retTys alts argAndTys)
    pure $ if isPoisonExpr `any` alts then PoisonExpr else
      Core (Match retTy altsMap Nothing) matchTy -- TODO def

  P.Lit l  → pure $ Core (Lit l) (TyGround [typeOfLit l])

  x → error $ "not implemented: inference of: " <> show x
