module Eval where
import FusionEnv
import Prim
import CoreSyn
import CoreUtils
import ShowCore()
import qualified Data.Vector.Mutable as MV
import qualified Data.IntMap as IM
--import qualified Data.Vector as V
import Control.Lens

-- Which args does a function case-split
data FuseArg
 = NoBranch  -- Not case-split in this function (Presumably its built into the result and may be case-split later)
 | CaseArg   -- arg is case-split
 | CaseFnArg [IName] -- arg is a fn whose result is case-split
 -- ^ We will want to know which partial applications of this produce a constant label
 -- This means knowing which Set of Args need to also be constant for this CaseFnArg to make a constant label
 | LensedArg {- Lens -} -- What structure of the arg must be known to fuse with a case

-- η-reduction => f x = g x     ⊢ f = g
-- β-reduction => (\x => f x) y ⊢ f y
-- The env contains a map of β-reducing args
simplifyBindings :: IName -> Int -> Int -> MV.MVector s Bind -> ST s (Simplifier s)
simplifyBindings modIName nArgs nBinds bindsV = do
  argSubs <- MV.generate nArgs (\i -> Var (VArg i))
  execStateT (simpleBind `mapM` [0 .. nBinds-1]) Simplifier {
    _thisMod     = modIName
  , _extBinds    = _ --allBinds
  , _cBinds      = bindsV
  , _nApps       = 0 -- measure the size of the callgraph
  , _argTable    = argSubs
  , _betaStack   = 0
  , _self        = _

  , _caseArgs    = emptyBitSet
  , _caseFnArgs  = emptyBitSet

  , _caseCount   = -1 -- counts negative labels
  , _streamCases = []
  , _streamOK    = True
  , _recLabels   = IM.empty
  }

-- very brutal; don't use this
inline :: QName -> SimplifierEnv s Term
inline q = use thisMod >>= \mod -> if modName q == mod
  then simpleBind (unQName q) <&> \(BindOpt nApps (Core t ty)) -> t
  else _

simpleBind :: Int -> SimplifierEnv s Bind
simpleBind n = use cBinds >>= \cb -> MV.read cb n >>= \b -> do
--traceM "\n"
  svN <- nApps <<.= 0
  self .= n
  MV.write cb n (BindOpt (complement 0) (Core (Var (VBind n)) tyBot)) -- recursion guard
  new <- case b of
    BindOpt nA body -> (nApps .= nA) *> pure body
    BindOK isRec (Core t ty) -> simpleTerm t <&> \case
      -- catch top level partial application (ie. extra implicit args)
      App (Instr (MkPAp n)) (f2 : args2) -> let
        (arTs , retT) = getArrowArgs ty
        diff = n - length args2
        in Core (PartialApp arTs f2 args2) retT
      newT -> Core newT ty
    x -> pure $ PoisonExpr
  napps <- nApps <<.= svN
  let b = BindOpt napps new
  MV.write cb n (BindOpt napps new)
  pure b

simpleTerm :: Term -> SimplifierEnv s Term
simpleTerm t = let
  in case t of
  Var v -> case v of
    VBind i  -> simpleBind i <&> \case
      BindOpt napps (Core new t) -> if False && napps < 1
        then new else Var (VBind i) -- directly inline small callgraphs
    VArg  i  -> use argTable >>= \at -> MV.read at i
    VQBind i -> pure (Var (VQBind i)) --inline i
    _ -> pure t

  Cast c a -> pure t

  Abs argDefs free body ty -> simpleTerm body <&> \b -> Abs argDefs free b ty
  App f args    -> simpleApp f args
  RecApp f args -> simpleApp f args

  Cons fields -> Cons <$> (simpleTerm `traverse` fields)
  TTLens (Cons fields) [f] op -> let
    fromMaybeF = fromMaybe (error $ "Type inference fail: field not present")
    in case op of
    LensGet   -> pure (fromMaybeF (fields IM.!? qName2Key f))
--  LensSet v -> simpleTerm v <&> (IM.insert (qName2Key f) v fields)

  Label l ars -> Label l <$> ((\(Core t ty) -> (`Core` ty) <$> simpleTerm t) `traverse` ars)
  Match ty branches d -> error "Unsaturated Match"

  _ -> pure t

foldAbs argDefs free body ty args = use argTable >>= \aT -> let
  ([] , trailingArgs , etaReducable) = partitionThese (align argDefs args)
  in do
  -- TODO If we're stacking β-reductions of a function, need to reset its args
  etaReducable `forM` \((i,ty) , arg) -> MV.write aT i arg
  bodyOpt <- simpleTerm body
  etaReducable `forM` \((i,ty) , arg) -> MV.write aT i (Var (VArg i))
  pure $ case trailingArgs of
    []  -> bodyOpt
    ars -> App bodyOpt ars

-- (do partial) β-reduction
simpleApp f args = (nApps %= (1+)) *> case f of
  Abs argDefs free body ty -> foldAbs argDefs free body ty args
  Instr i -> (simpleTerm `mapM` args) <&> \args -> simpleInstr i args
  Match retT branches d | [scrut] <- args -> fuseMatch retT scrut branches d
  fn -> simpleTerm fn >>= \case
    Abs argDefs' free body ty -> foldAbs argDefs' free body ty args
    fn -> App fn <$> (simpleTerm `mapM` args)

-- Fusing Matches with constant labels is the main point of this exercise
fuseMatch :: Type -> Term -> IntMap Expr -> Maybe Expr -> SimplifierEnv s Term
fuseMatch ty scrut' branches d = simpleTerm scrut' >>= \scrut -> let this = App (Match ty branches d) [scrut]
  in case scrut of
  -- Ideal: case-of-label
  Label l params -> let getTerm (Just (Core t ty)) = t
    in pure $ App (getTerm ((branches IM.!? qName2Key l) <|> d)) ((\(Core t ty) -> t) <$> params)

  -- Near-Ideal: case-of-case: push outer case into each branch of the inner Case
  -- frequently the inner case can directly fuse with the outer cases output labels
  App (Match ty2 innerBranches innerDefault) [innerScrut] -> let
    pushCase (Core (Abs ars free body ty) _ty) = do
      branch <- simpleApp (Match ty branches d) [body] >>= simpleTerm -- TODO why is this necessary
      let newTy = case branch of { Abs _ _ _ t -> t ; _ -> tyBot } -- don't gamble with the actual ty
      pure   (Core (Abs ars free branch newTy) newTy)
    in do
      optBranches <- innerBranches `forM` pushCase
      optD <- maybe (pure Nothing) (fmap Just . pushCase) d
      pure (App (Match ty2 optBranches optD) [innerScrut])

  -- case-of-App: Hope to get a constant label after beta-reduction
  App (Var (VQBind caseFnArg)) ars -> inline caseFnArg >>= \f -> simpleApp f ars >>= \scrutInline ->
    fuseMatch ty scrutInline branches d

  -- vv Require ourselves to be inlined at call-sites

  -- case-of-Arg: β-reduction on this Arg will fuse
  -- case-merge: Check if any branches also case this Arg
  Var (VArg caseArg) -> this <$ (caseArgs %= (`setBit` caseArg))

  -- case-of-AppArg:
  -- Now both the fn Arg and (some of) these current args must be known
  -- Fn may be able to produce a constant label given only some constant args
--App (Var (VArg caseFnArg)) ars -> this <$ (caseFnArgs %= (`setBit` caseFnArg))

  -- Any simple (esp TTCalculus) function of an Arg is worth noting
  -- if the arg is static up-to this lens/prism, it will fuse on β-reducing this F
  -- ~ ac is some lens/prism on the Arg that we need to know
--_ | Just ac <- getLens scrut ->

  _ -> pure this

-- Try derive a Lens into an Arg
getLens :: Term -> Maybe Term = const Nothing

{-
-- a Case on one of the arguments
mkSvState retT branches d arg = mdo
  newCase <- caseCount <<%= (1+)
--addStreamCase c

  bs <- branches `forM` \b -> simpleTerm b >>= \(Abs ars is t ty) -> do
    -- pack all needed state
    this <- use self
    vars <- use caseState
    resetCaseState
    let new = case t of
          -- Match over labels is perfect for stream fusion
          -- If any of the args are a self recursive call, save a CASE0 in their place
          Label i ars  -> let
            case0 = Label (-1)
            in
            checkRec <$> ars
          App (Var (VBind i)) ars | i == this -> _

          -- Sv free vars into CASEN marker
          App (Match _retT subBranches d) [ars] -> _

--        App f ars ->

          -- Cannot stream this; foldl over a builder accumulator must switch to build-cata
          x         -> x
    use streamOK <&> \case
      True  -> new
      False -> Abs ars is t ty
  pure bs
-}

simpleInstr i args = case i of
  GMPInstr j -> simpleGMPInstr j args
  Zext | [Lit (Int i)]   <- args -> Lit (Fin 64 i)
       | [Lit (Fin n i)] <- args -> Lit (Fin 64 i)
  i -> App (Instr i) args

simpleGMPInstr :: NumInstrs -> [Term] -> Term
simpleGMPInstr i args = let
  mkCmpInstr pred args = App (Instr (NumInstr (PredInstr pred))) args
  in case i of
  IntInstr Add
    | [Cast (CastInstr (GMPZext n)) (Lit (Int i)) , rarg] <- args -> App (Instr (GMPOther AddUI)) [Lit (Fin 64 i) , rarg]
    | [larg , Cast (CastInstr (GMPZext n)) (Lit (Int i))] <- args -> App (Instr (GMPOther AddUI)) [Lit (Fin 64 i) , larg]
    | _ <- args -> App (Instr (GMPInstr i)) args
  IntInstr Sub
    | [Cast (CastInstr (GMPZext n)) (Lit (Int i)) , rarg] <- args -> App (Instr (GMPOther UISub)) [Lit (Fin 64 i) , rarg]
    | [larg , Cast (CastInstr (GMPZext n)) (Lit (Int i))] <- args -> App (Instr (GMPOther SubUI)) [larg , Lit (Fin 64 i)]
    | _ <- args -> App (Instr (GMPInstr i)) args
  IntInstr Mul
    -- ? MulUI
    | [Lit (Fin 64 i) , rarg] <- args -> App (Instr (GMPOther MulSI)) args
    | [larg , Lit (Fin 64 i)] <- args -> App (Instr (GMPOther MulSI)) [Lit (Fin 64 i) , larg]
  PredInstr LECmp -- TODO other cmp types
    -- CMPAbsD CMPAbsUI
    -- TODO spawn the icmp instruction here
    | [Cast (CastInstr (GMPZext n)) (Lit (Int i)) , rarg] <- args ->
        mkCmpInstr GECmp [App (Instr (GMPOther CMPUI)) [rarg , Lit (Fin 64 i)] , Lit (Fin 32 0)] -- flip the icmp
    | [larg , Cast (CastInstr (GMPZext n)) (Lit (Int i))] <- args ->
        mkCmpInstr LECmp [App (Instr (GMPOther CMPUI)) [larg , Lit (Fin 64 i)] , Lit (Fin 32 0)]
  IntInstr IPow
    -- powmui ?
    | [Lit (Fin 64 _) , Lit (Fin 64 _)] <- args -> App (Instr (GMPOther UIPowUI)) args
    | [larg , Lit (Fin 64 _)]           <- args -> App (Instr (GMPOther PowUI)) args
  -- nothing to fold
  i -> App (Instr (GMPInstr i)) args
