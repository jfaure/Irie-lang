module TTCalculus (ttApp , normaliseType) where
import Prim
import CoreSyn
import Errors()
import CoreUtils
import TCState
import Data.List(span)
import qualified Data.IntMap as IM

-- Application of TTs (combinations of terms and types)
-- TTs can be promoted to higher universes, but not demoted
-- Types can be indexed by Terms, the resulting expression is a Type
-- Lambda calculus TTs are ambiguous, eg. 'f x = x' could be a type or a term
-- Terms that need to become types need to have potential fixed points converted to µ types
-- This has to be done in TCState because forward refs may trigger inference mid ttApp
ttApp ∷ Type → (Int → TCEnv s Expr) → Expr → [Expr] → TCEnv s Expr
ttApp retTy readBind fn args = let --trace (clYellow (show fn <> " $ " <> show args ∷ Text)) $ let
--getQBind q = use thisMod ≫= \modIName → use openModules ≫= \open → use externs ≫= \e →
--  handleExtern (readQParseExtern open modIName e (modName q) (unQName q))
  ttApp' = ttApp retTy readBind

  -- Term application
  doApp coreFn args = let
    (termArgs , otherArgs) = span (\case {Core{}→True ; _→False}) args
    app = App coreFn $ (\(Core t _ty)→t) <$> termArgs -- forget the argument types
    in pure $ case otherArgs of
      []  → Core app retTy
      tys → if any isPoisonExpr tys then PoisonExpr else error $ "ttApp cannot resolve application: " <> show app <> show tys

{- -- Eta reduction of Pi types applied to Exprs (likely result is an indexed type family)
  substituteType ∷ Maybe (QName , [Expr]) → IM.IntMap Expr → Type → Type
  substituteType self piArgs body = let
    sT = substituteType self piArgs
    in case body of
    TyGround [THTyCon t] → TyGround . (:[]) . THTyCon $ case t of
      THSumTy alts → THSumTy $ sT <$> alts
      THTuple alts → THTuple $ sT <$> alts
      x → error $ show x

    -- Expr must be lambda calculus or product/sumtype operations
    TyTerm e t → case term2Type self piArgs e of
      (Just m , t) → TyGround [THMu 0 t]
      (_ , t) → t
    _ → body
-}

  in case fn of
  PoisonExpr → pure PoisonExpr
  Core cf _ty → case cf of
--  Var (VQBind q) → getQBind q ≫= \e → case e of
--    Core (Var (VQBind j)) _ty | j == q → doApp cf args
--    e → ttApp' e args

--  Special instructions (esp. type constructors)
    Instr (TyInstr Arrow)  → expr2Ty readBind `mapM` args <&> \case
      { [a , b] → Ty (TyGround (mkTyArrow [a] b)) ; x → error $ "wrong arity for TyArrow" <> show x }
    Instr (TyInstr MkIntN) | [Core (Lit (Int i)) _ty] ← args →
      pure $ Ty (TyGround [THPrim (PrimInt $ fromIntegral i)])
    Instr (MkPAp _n) | f : args' ← args → ttApp' f args'
    coreFn → doApp coreFn args
  Ty f → pure $ Ty (TyIndexed f args) -- make no attempt to normalise types at this stage

--  _ → PoisonExpr <$ (errors . typeAppFails %= (BadTypeApp f args :))
  _ → error $ "ttapp: unexpected 'function': " <> show fn <> " $ " <> show args

-- inline aliases and eta-reduce TyPi applications
normaliseType ∷ IM.IntMap Expr → Type → TCEnv s Type
normaliseType args ty = let
--getQBind q = use thisMod ≫= \modIName → use openModules ≫= \open → use externs ≫= \e →
--  handleExtern (readQParseExtern open modIName e (modName q) (unQName q))

  -- If the term isn't a type index, it must be lambda calculus or product/sumtype operations
--term2Type ∷ IM.IntMap Expr → Term → _ Type
  term2Type _piArgs = \case
--  Var (VArg i)   → pure $ case piArgs IM.!? i of
--    Just (Ty t) → t
--    _ → (TyGround [THPoison])
--  RecApp _f args → let recArgs = (\case { Var (VArg i) → i ; _ → (-1) }) <$> args
--    in pure $ if all (`IM.member` piArgs) recArgs then (TyGround [THMuBound 0])
--      else _
--  Var (VQBind q) → _
--  App f args     → _
    x → error $ show x

  normaliseTH args = \case
    THTyCon t → THTyCon <$> case t of
      THArrow ars r → THArrow   <$> (normaliseType args `mapM` ars) <*> normaliseType args r
      THSumTy ars   → THSumTy   <$> (normaliseType args `mapM` ars)
      THTuple ars   → THTuple   <$> (normaliseType args `mapM` ars)
      THProduct ars → THProduct <$> (normaliseType args `mapM` ars)
      _ → _
    THMu m t → THMu m <$> normaliseType args t
    ok → pure $ case ok of
      THPrim{} → ok
      ko → error $ show ko

  normalisePiApp piArgs body tyArgs = let -- TODO check arg types match piArg types !
    pn = length piArgs ; an = length tyArgs
    (ok , _rest) = splitAt an piArgs
    in if pn == an -- check if args are the same in recursive applications
    then let --self = Nothing --(,args) <$> this
      in normaliseType (IM.fromList (zipWith (\(i,_t) e → (i,e)) ok tyArgs)) body
    else _ --TySi (Pi rest body) (foldl (\m (i , val) → IM.insert (i , val) m) args tyArgs

  in case ty of
  TyIndexed (TyPi (Pi piArgs body)) tyArgs → normalisePiApp piArgs body tyArgs
--TyIndexed (TyAlias q) tyArgs → getQBind q ≫= \case
--  Ty t → case t of
--    TyPi (Pi piArgs body) → normalisePiApp piArgs body tyArgs
--    TyGround g → TyGround <$> normaliseTH args `mapM` g
--    t → pure t
--  x → error $ "not a type: " <> show x
  TyGround ts → TyGround <$> normaliseTH args `mapM` ts
  TyTerm e _t → term2Type args e
  t → pure t
