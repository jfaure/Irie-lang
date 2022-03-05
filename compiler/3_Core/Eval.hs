module Eval where
import FusionEnv
import Prim
import CoreSyn
import PrettyCore
import CoreUtils
import ShowCore()
import qualified Data.Vector.Mutable as MV
import qualified Data.IntMap as IM
import qualified Data.Vector as V
import Data.List (unzip3)
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
  letSpecs'   <- MV.replicate 32 Nothing
  tmpSpecs'   <- MV.new 32
  argSubs     <- MV.generate nArgs (\i -> Var (VArg i))
  execStateT (simpleBind `mapM` [0 .. nBinds-1]) Simplifier {
    _thisMod     = modIName
  , _extBinds    = _ --allBinds
  , _cBinds      = bindsV
  , _nApps       = 0 -- measure the size of the callgraph
  , _argTable    = argSubs
  , _bruijnArgs  = V.empty
  , _self        = _

  , _nSpecs      = 0
  , _letSpecs    = letSpecs'
  , _tmpSpecs    = tmpSpecs'
  , _specStack   = emptyBitSet
  , _inlineStack = emptyBitSet

  , _caseArgs    = emptyBitSet
  , _caseFnArgs  = emptyBitSet
  }

addTmpSpec :: QName -> IName -> [Term] -> SimplifierEnv s IName
addTmpSpec q bruijnN args = do
  s' <- use tmpSpecs 
  n  <- nSpecs <<%= (1+)
  s  <- (tmpSpecs <.=) =<< (if MV.length s' <= n then MV.grow s' 32 else pure s')
  let hackN = (if n == 1 then 1 else 0)
  n <$ MV.write s n (q , bruijnN , args)

-- very brutal
inline :: QName -> SimplifierEnv s Term
inline q = use thisMod >>= \mod -> use inlineStack >>= \is -> let
  unQ = unQName q
  in if modName q == mod && (not (is `testBit` unQ))
  then (inlineStack %= (`setBit` unQ)) *> simpleBind unQ <&> \(BindOpt nApps (Core t ty)) -> t
  else pure (Var (VQBind q))

simpleBind :: Int -> SimplifierEnv s Bind
simpleBind bindN = use cBinds >>= \cb -> MV.read cb bindN >>= \b -> do
  mod <- use thisMod
  svN <- nApps <<.= 0
  specStack .= emptyBitSet
  svIS <- inlineStack <<.= emptyBitSet
--svIS <- use inlineStack
  self .= bindN
  -- VBinds are not present in the inferred Syn; they are thus only introduced at this recursion guard
  MV.write cb bindN (BindOpt (complement 0) (Core (Var (VBind bindN)) tyBot)) -- recursion guard

  new' <- case b of
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
  inlineStack .= svIS

  -- If recursive specialisations needed, do them then resimplify
  new   <- (nSpecs <<.= 0) >>= \case
    0 -> pure new'
    n -> use tmpSpecs >>= \t -> use letSpecs >>= \ls -> do
      traceM ("spec at Bind: " <> show bindN)
      let Core thisF ty = new'
      [0 .. n-1] `forM` \i -> MV.read t i >>= \(q , bruijnN , argStructure) -> do
--     | not (modName q == mod && unQName q == bindN) -> traceM $ "mutual specialisation: " <> show argStructure
--     | otherwise -> do
--      unless (modName q == mod && unQName q == bindN) (error $ "mutual specialisation(?): " <> show q <> show bindN)
        specF <- if modName q == mod && unQName q == bindN then pure thisF else inline q
        specStack .= emptyBitSet
        traceM ("specialising: " <> prettyTermRaw specF <> "\n on:") *> (argStructure `forM` (traceM . prettyTermRaw))

        spec <- BruijnAbs bruijnN <$> simpleApp specF argStructure
        MV.write ls i (Just spec)
        traceM $ "specialised(" <> show i <> ") " <> prettyTermRaw spec

      -- re-simplify this to inline and further simplify the (Spec i) we just derived
      specStack .= emptyBitSet
--    pure (Core thisF ty)
      simpleTerm thisF <&> \tok -> Core tok ty

  let b = BindOpt napps new
  MV.write cb bindN (BindOpt napps new)
  pure b

-- Recurse everywhere hoping to fuse Matches with Labels
simpleTerm :: Term -> SimplifierEnv s Term
simpleTerm t = -- (traceM $ (prettyTermRaw t) <> "\n\n") *>
  case t of
  Var v -> case v of
--  VBind i  -> simpleBind i <&> \case
--    BindOpt napps (Core new t) -> if False && napps < 1 then new else Var (VBind i)
    VArg  i  -> use argTable >>= \at -> MV.read at i --  <&> \a -> d_ (i,a) a
    VQBind i -> pure (Var (VQBind i))
    _ -> pure t
  VBruijn i -> use bruijnArgs <&> \v -> if V.length v /= 0 then (v V.! i) else VBruijn i

  Abs argDefs free body ty -> simpleTerm body <&> \b -> Abs argDefs free b ty
  BruijnAbs n body -> simpleTerm body <&> BruijnAbs n

  App f args    -> simpleApp f args
  RecApp f args -> simpleRecApp f args -- Don't want to inline fn into itself

  Cons fields -> Cons <$> (simpleTerm `traverse` fields)
  TTLens (Cons fieldsRaw) [f] op -> (simpleTerm `traverse` fieldsRaw) >>= \fields -> let
    fromMaybeF = fromMaybe (error $ "Type inference fail: field not present")
    in case op of
    LensGet   -> pure (fromMaybeF (fields IM.!? qName2Key f))
--  LensSet v -> simpleTerm v <&> (IM.insert (qName2Key f) v fields)

  Label l ars -> Label l <$> (simpleTerm `traverse` ars)

  Spec i unstructuredArgs -> (specStack <<%= (`setBit` i)) >>= \sp -> use letSpecs >>= \ls -> MV.read ls i >>= \case
--  Just spec -> simpleApp spec unstructuredArgs
    Just spec | not (sp `testBit` i) -> simpleApp spec unstructuredArgs
    _   -> pure t

--Match ty branches d -> error "Unsaturated Match"
--Cast c a -> pure t
--Lit{}    -> pure t
  _ -> pure t

-- Recursive specialisation of F: an Abs over unpacked elements of arg structures
-- The body is the result of simplifying inline F applied to the original structure (with unpacked elems abstracted)
-- This will eliminate all the structure that F inspects (which may not be all of it)
mkRecSpecialisation :: QName -> [Term] -> SimplifierEnv s Term
mkRecSpecialisation q args = let
  -- replace all Label args with new deBruijn ArgNames , pass those to the specialisation
  unPackArg :: Int -> Term -> (Int , [Term] , Term) -- bruijnN , (new Args(label sub-exprs) , abstracted args
  unPackArg argCount = \case
    Label l ars -> let
      raw = unPackArg argCount <$> ars
      (done , argCount') = let
        go arg (len , extraArs , wrapped) = if len == 0
          then gets identity >>= \ac -> (1 , arg : extraArs , VBruijn ac) <$ modify (1+)
          else modify (len+) $> (len , extraArs , wrapped)
        in zipWithM go ars raw `runState` argCount
      (lens , extraArs , wrapped) = unzip3 done
      in (argCount' , concat extraArs , Label l wrapped) -- (VBruijn <$> [argCount .. len-1]))
    x -> (argCount , [] , x)

  (  bruijnN          -- number of new arguments
   , unStructuredArgs -- subexpressions of labels
   , repackedArgs     -- original arguments with label subexpressions renamed
   ) = let addArg (bruijnN , newArgs' , absArgs') nextArg = let
            (bruijnN' , newArgs , absArgs) = unPackArg bruijnN nextArg
            in (bruijnN' , newArgs : newArgs' , absArgs : absArgs')
   in foldl' addArg (0 , [] , []) args
  in (`Spec` (concat unStructuredArgs)) <$> addTmpSpec q bruijnN (reverse repackedArgs)
  -- once this rec-fn is simplfied once, need to simplify its specialisations `App q repackedArgs` then sub them in

-- Perform β-reduction on an Abs (! doesn't simplify its args)
foldAbs argDefs free body ty args = use argTable >>= \aT -> let
  (resArgDefs , trailingArgs , betaReducable) = partitionThese (align argDefs args)
  in do
  -- TODO If we're stacking β-reductions of a function, need to reset its args
  sv <- betaReducable `forM` \((i,ty) , arg) -> ((i,) <$> MV.read aT i) <* MV.write aT i arg
--betaReducable `forM` \((i,ty) , arg) -> traceM $ show i <> " " <> prettyTermRaw arg
  b2 <- simpleTerm body
  sv `forM` \(i , arg) -> MV.write aT i arg
  bodyOpt <- case b2 of
    App f@Abs{} ars -> simpleApp f ars
    x -> pure x
  when (not (null resArgDefs)) (traceM $ "resArgDefs! " <> show resArgDefs)
  pure $ case trailingArgs of
    []  -> bodyOpt
    ars -> App bodyOpt ars

foldBruijn n body args = let
  argSubs = V.fromList args
  in do
  when (V.length argSubs /= n) (error $ "bad bruijn: args (" <> show (V.length argSubs) <> ") expected: " <> show n)
  bruijnArgs .= argSubs
  simpleTerm body <* (bruijnArgs .= V.empty)

isSpecArg = \case { Label{}->True ; Match{}->True ; _->False}
-- (do partial) β-reduction
simpleRecApp f argsRaw = simpleTerm f >>= \f' -> (simpleTerm `traverse` argsRaw) >>= simpleApp' True  f'
simpleApp    f argsRaw = simpleTerm f >>= \f' -> (simpleTerm `traverse` argsRaw) >>= simpleApp' False f'

simpleApp' :: Bool -> Term -> [Term] -> SimplifierEnv s Term
simpleApp' isRec f args = (nApps %= (1+)) *> case f of
  App f2 args2 -> simpleTerm f2 >>= \f2' -> simpleApp' isRec f2' (args2 ++ args)
  BruijnAbs n body -> foldBruijn n body args
  Abs argDefs free body ty -> foldAbs argDefs free body ty args
  Instr i -> pure $ simpleInstr i args
  Match retT branches d | [scrut] <- args -> fuseMatch retT scrut branches d
  fn -> let app f a = if isRec then RecApp f a else App f a
    in case fn of
    Abs argDefs' free body ty -> foldAbs argDefs' free body ty args
    Var (VQBind q) -> let
      in if not (null args) && any isSpecArg args -- && all (\case { Var (VArg{}) -> False ; _ -> True }) args
      then if isRec
        then mkRecSpecialisation q args
        else inline q >>= \case
          Var{} -> pure (app fn args)
          fInline -> simpleApp' isRec fInline args
      else pure (app fn args)
    _ -> pure (app fn args)

-- Fusing Matches with constant labels is the main goal
fuseMatch :: Type -> Term -> IntMap Expr -> Maybe Expr -> SimplifierEnv s Term
fuseMatch ty scrut' branchesRaw d = simpleTerm scrut' >>= \scrut ->
  ((\(Core t ty) -> (`Core` ty) <$> simpleTerm t) `traverse` branchesRaw) >>= \branches -> let
    this = App (Match ty branches d) [scrut]
  in case scrut of
  -- Ideal: case-of-label
  Label l params -> let getTerm (Just (Core t ty)) = t
    in pure $ App (getTerm ((branches IM.!? qName2Key l) <|> d)) params

  -- Near-Ideal: case-of-case: push outer case into each branch of the inner Case
  -- frequently the inner case can directly fuse with the outer cases output labels
  App (Match ty2 innerBranches innerDefault) [innerScrut] -> let
    pushCase (Core (Abs ars free body ty) _ty) = do
      branch <- simpleApp (Match ty branches d) [body] >>= simpleTerm {-why?-}
      let newTy = case branch of { Abs _ _ _ t -> t ; _ -> tyBot } -- lost the Ty
      pure   (Core (Abs ars free branch newTy) newTy)
    in do
      optBranches <- innerBranches `forM` pushCase
      optD <- maybe (pure Nothing) (fmap Just . pushCase) d
      pure (App (Match ty2 optBranches optD) [innerScrut])

  -- case-of-App: Hope to get a constant label after beta-reduction
  App (Var (VQBind caseFnArg)) ars {-| all (\case {Var (VArg{}) -> False ; _ -> True}) ars-} -> inline caseFnArg >>= \f ->
    simpleApp f ars >>= \scrutInline -> fuseMatch ty scrutInline branches d

  -- vv fusing Case-of- TTCalculus(product/Label/Abs) on args requires specialisations

  -- case-of-Arg: β-reduction on this Arg will fuse
  -- case-merge: Check if any branches also case this Arg
  Var (VArg caseArg) -> this <$ (caseArgs %= (`setBit` caseArg))

  -- case-of-AppArg:
  -- Now both the fn Arg and (some of) these current args must be known
  -- Fn may be able to produce a constant label given only some constant args
--App (Var (VArg caseFnArg)) ars -> this <$ (caseFnArgs %= (`setBit` caseFnArg))

  -- advertise specialisations for args static up to this lens/prism
  -- ~ ac is a lens/prism on the Arg that we need to know
--_ | Just ac <- getLens scrut ->

  _ -> pure this

-- Try derive a Lens into an Arg
getLens :: Term -> Maybe Term = const Nothing

simpleInstr i args = case i of
  IfThenE | [cond , a , b] <- args
          , App pred [Lit (Int x) , Lit (Int y)] <- cond -> case pred of
    Instr (NumInstr (PredInstr p)) -> 
      if case p of { EQCmp-> x == y ; NEQCmp-> x /= y ; GECmp-> x > y ; GTCmp-> x >= y ; LECmp-> x <= y ; LTCmp-> x < y }
      then a else b
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
