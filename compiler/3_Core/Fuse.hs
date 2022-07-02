-- Simplification pass on Core syntax
module Fuse (simplifyBindings) where
import FusionEnv
import SimplifyInstr
import Prim
import CoreSyn
import PrettyCore
import CoreUtils
import ShowCore()
import qualified Data.Vector.Mutable as MV
import qualified BitSetMap as BSM
import qualified Data.Map as M
import qualified Data.Vector as V
import Data.List (unzip3)
import Control.Lens

-- η-reduction => f x = g x     ⊢ f = g
-- β-reduction => (\x => f x) y ⊢ f y
-- The env contains a map of β-reducing args
simplifyBindings :: IName -> Int -> Int -> MV.MVector s Bind -> ST s (Simplifier s)
simplifyBindings modIName nArgs nBinds bindsV = do
  letSpecs'   <- MV.replicate 32 Nothing
  tmpSpecs'   <- MV.new 32
  bindSpecs'  <- MV.replicate nBinds emptyBitSet
  cachedSpecs'<- MV.replicate nBinds mempty
  argSubs     <- MV.generate nArgs (\i -> Var (VArg i))
  (simpleBind `mapM` [0 .. nBinds-1] {-*> doReSpecs-}) `execStateT` Simplifier {
    _thisMod     = modIName
  , _extBinds    = _ --allBinds
  , _cBinds      = bindsV
  , _nApps       = 0 -- measure the size of the callgraph
  , _useArgTable = False
  , _argTable    = argSubs
  , _bruijnArgs  = V.empty
  , _self        = _

  , _nSpecs      = 0
  , _prevSpecs   = 0 -- lags behind nSpecs
  , _letSpecs    = letSpecs'
  , _bindSpecs   = bindSpecs'
  , _cachedSpecs = cachedSpecs'
  , _tmpSpecs    = tmpSpecs'
  , _thisSpec    = -1
  , _recSpecs    = emptyBitSet

  -- Binds needing to be re-specialised
  , _hasSpecs    = emptyBitSet
  , _reSpecs     = []

  , _specStack   = emptyBitSet
  , _inlineStack = emptyBitSet

  , _caseArgs    = emptyBitSet
  , _caseFnArgs  = emptyBitSet
  }

--doReSpecs = use reSpecs >>= \re -> re `forM` \i -> (specStack .= emptyBitSet) *> reSimpleBind i

addTmpSpec :: Either QName IName -> IName -> [Term] -> SimplifierEnv s IName
addTmpSpec q bruijnN args = do
  s' <- use tmpSpecs 
  n  <- nSpecs <<%= (1+)
  s  <- (tmpSpecs <.=) =<< (if MV.length s' <= n then MV.grow s' 32 else pure s')
--traceM ("tmpSpec: " <> show n <> " " <> show q <> " " <> show args)
  n <$ MV.write s n (q , bruijnN , args)

-- very brutal
inline :: QName -> SimplifierEnv s Term
inline q = use thisMod >>= \mod -> use inlineStack >>= \is -> let
  unQ = unQName q
  in if modName q == mod && (not (is `testBit` unQ))
  then (inlineStack %= (`setBit` unQ)) *> simpleBind unQ <&> \(BindOpt nApps nSpecs (Core t ty)) -> t
  else pure (Var (VQBind q))

--reSimpleBind bindN = traceM ("re: " <> show bindN) *> use cBinds >>= \cb -> MV.read cb bindN >>= \(BindOpt n s (Core t ty)) -> do
--  mod <- use thisMod
--  specialiseRequests bindN mod (Core t ty)
--  simple <- simpleTerm t
--  let done = BindOpt n s (Core simple ty)
--  done <$ MV.write cb bindN done

simpleBind :: Int -> SimplifierEnv s Bind
simpleBind bindN = use cBinds >>= \cb -> MV.read cb bindN >>= \b -> do
  mod <- use thisMod
  svN <- nApps <<.= 0
  specStack .= emptyBitSet
  svIS <- inlineStack <<.= emptyBitSet
  svHS <- hasSpecs <<.= emptyBitSet
  self .= bindN
  -- VBinds are not present in the inferred Syn; they are thus only introduced here
  MV.write cb bindN (BindOpt (complement 0) emptyBitSet (Core (Var (VBind bindN)) tyBot)) -- recursion guard

  new' <- case b of
    BindOpt nA bs body -> (nApps .= nA) *> pure body
    BindOK isRec (Core t ty) -> simpleTerm t <&> \case
      -- catch top level partial application (ie. extra implicit args)
      App (Instr (MkPAp n)) (f2 : args2) -> let
        (arTs , retT) = getArrowArgs ty
        diff = n - length args2
        in Core (PartialApp arTs f2 args2) retT
      newT -> Core newT ty
    x -> pure $ PoisonExpr

  inlineStack .= svIS
  futureSpecs <- hasSpecs <<.= svHS
  napps <- use nApps

  when (futureSpecs /= 0) $ do
    traceM ("HasSpecs: " <> show (bindN , bitSet2IntList futureSpecs))
    reSpecs %= (bindN:)

  specialiseRequests bindN mod new'

  -- After deriving the specs; resimplify to inline the specs and further simplify
  new <- case new' of { Core thisF ty -> simpleTerm thisF <&> \tok -> Core tok ty }

  nApps .= svN
  let bs = case b of { BindOpt _ s _ -> s ; _ -> emptyBitSet }
      newB = BindOpt napps bs new
  newB <$ MV.write cb bindN newB

-- Binds request specialisations which are derived here
specialiseRequests bindN mod new' = use nSpecs >>= \nspecs -> (prevSpecs <<.= nspecs) >>= \prevspecs ->
  when (prevspecs /= nspecs) $ use tmpSpecs >>= \t -> let Core thisF ty = new' in do
    respecs <- [prevspecs .. nspecs - 1] `forM` \i -> MV.read t i >>= \(q , bruijnN , argStructure) -> case q of
      Left q  -> specialiseBind bindN mod thisF q i bruijnN argStructure
      Right j -> do -- specialise specialisation
        -- TODO merge specs and check the cache
        Just specF <- use letSpecs >>= \ls -> MV.read ls j
        spec <- specialiseTerm i bruijnN specF (getArgShape <$> argStructure) argStructure
        traceM $ "specialised " <> show i <> " (specialisation " <> show j <> ") " <> prettyTermRaw spec <> "\n"
        pure []
    thisSpec .= -1
    (concat respecs) `forM` simpleBind -- inlines specialisations

    -- re-simplify this to inline and further simplify the spec we just derived
    specStack   .= emptyBitSet
    inlineStack .= emptyBitSet

specialiseTerm :: IName -> Int -> Term -> p -> [Term] -> SimplifierEnv s Term
specialiseTerm i bruijnN specF argShapes argStructure = let
  free = case specF of { Abs ars free t ty -> free ; BruijnAbs bn free t -> free ; _ -> emptyBitSet }
  in simpleApp specF argStructure >>= \case -- specBody
  -- TODO should avoid producing this in the first place perhaps
--  App (Spec proxy) [] -> (BruijnAbs bruijnN free (Spec proxy)) <$ traceM ("proxy " <> show i <> " == " <> show proxy)
    specBody -> let spec = BruijnAbs bruijnN free specBody in do
      traceM $ "specialised " <> show i <> prettyTermRaw spec <> "\n"
      spec <$ (use letSpecs >>= \ls -> MV.write ls i (Just spec))

specialiseBind :: IName -> ModIName -> Term -> QName -> IName -> Int -> [Term] -> SimplifierEnv s [Int]
specialiseBind bindN mod thisF q i bruijnN argStructure = let
  unQ = unQName q
  argShapes = getArgShape <$> argStructure
  cacheSpec s = use cachedSpecs >>= \cs -> MV.modify cs (M.insert argShapes i) bindN
  in do
  specF <- if modName q == mod && unQName q == bindN then pure thisF else inline q
  specStack .= emptyBitSet
--traceM ("specialising " <> show i <> ": " <> prettyTermRaw specF <> "\n on:")*>(argStructure `forM` (traceM . prettyTermRaw))
  if modName q == mod && unQ == bindN
    then [] <$ (specialiseTerm i bruijnN specF argShapes argStructure >>= cacheSpec)
    else use bindSpecs >>= \bs -> MV.read bs bindN >>= \bindspecs -> use letSpecs >>= \ls -> do
      MV.modify bs (`setBit` i) unQ
      use cachedSpecs >>= \cs -> MV.read cs unQ <&> (M.!? argShapes) >>= \case
        Just reuse -> [unQ] <$ MV.write ls i (Just (Spec reuse)) <* traceM ("re-use specialisation: " <> show i <> " => " <> show reuse)
        Nothing    -> [unQ] <$ specialiseTerm i bruijnN specF argShapes argStructure

-- Recurse everywhere trying to fuse Matches with Labels
-- ! Simplifying a term twice can be flat out incorrect since Arg subs can contain functions of 'themselves'
-- eg. (after some inlining): `(\x => f x) (g x)` where x is literally the same arg
simpleTerm :: Term -> SimplifierEnv s Term
simpleTerm t = -- (traceM $ (prettyTermRaw t) <> "\n\n") *>
  case t of
  Var v -> case v of
    -- ! Arg substitutions may contain functions of 'themselves' these must not be substituted again in this App
    VArg  i  -> use useArgTable >>= \case
      False -> pure t
      True  -> use argTable >>= \at -> MV.read at i -- >>= \a -> a <$ traceM ("argSub: " <> show (i,a))
    VQBind i -> pure (Var (VQBind i))
    _ -> pure t
  VBruijn i -> use bruijnArgs <&> \v -> if V.length v /= 0 then (v V.! i) else VBruijn i

  Spec i -> pure t

  Abs argDefs free body ty -> simpleTerm body <&> \b -> Abs argDefs free b ty
  BruijnAbs n free body -> simpleTerm body <&> BruijnAbs n free
  App f args    -> simpleApp f args
  RecApp f args -> simpleRecApp f args

  Cons fields -> Cons <$> (simpleTerm `traverse` fields)
  TTLens (Cons fieldsRaw) [f] op -> (simpleTerm `traverse` fieldsRaw) >>= \fields -> let
    fromMaybeF = fromMaybe (error $ "Type inference fail: field not present")
    in case op of
    LensGet   -> pure (fromMaybeF (fields BSM.!? qName2Key f))
--  LensSet v -> simpleTerm v <&> (IM.insert (qName2Key f) v fields)

  Label l ars -> Label l <$> (simpleTerm `traverse` ars)
  Match ty branches d -> let simpleExpr (Core t ty) = simpleTerm t <&> \t' -> Core t' ty
    in Match ty
    <$> (simpleExpr `traverse` branches)
    <*> maybe (pure Nothing) (fmap Just . simpleExpr) d

  Cast c a -> Cast c <$> simpleTerm a
  Lit{}    -> pure t
  Instr{}  -> pure t
  Poison{} -> pure t
  _ -> error $ show t

-- specialisation of F: an Abs over unpacked elements of arg structures
-- The body is the result of simplifying inline F applied to the original structure (with unpacked elems abstracted)
-- This will eliminate all the structure that F inspects (maybe not all of it)
mkSpecialisation :: Either QName IName -> [Term] -> SimplifierEnv s Term
mkSpecialisation q args = let
  -- replace all Label args with new deBruijn ArgNames , pass those to the specialisation
  -- TODO also handle Cons !
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
  in do -- d_ (args , (bruijnN , unStructuredArgs , repackedArgs)) $
    i <- addTmpSpec q bruijnN (reverse repackedArgs)
    hasSpecs %= (`setBit` i)
    pure (App (Spec i) (concat unStructuredArgs))
  -- once this rec-fn is simplfied once, need to simplify its specialisations `App q repackedArgs` then sub them in

-- Perform β-reduction on an Abs
-- ! Have to simplify the body (again)
-- Note. if some arg is substituted with a fn of itself (while deriving specialisations), do not β-reduce it there
-- ie. Excessive calls to simpleTerm are incorrect, not just inefficient
foldAbs argDefs free body ty args = use argTable >>= \aT -> let
  (resArgDefs , trailingArgs , betaReducable) = partitionThese (align argDefs args)
  in do
  svUseAt <- useArgTable <<.= True
  sv <- betaReducable `forM` \((i,ty) , arg) -> ((i,) <$> MV.read aT i) <* MV.write aT i arg
  bodyOpt <- simpleTerm body -- Simplify and beta-reduce args
  useArgTable .= svUseAt
  sv `forM` \(i,arg) -> MV.write aT i arg

  when (not (null resArgDefs)) (traceM $ "resArgDefs! " <> show resArgDefs)
  pure $ case trailingArgs of
    []  -> bodyOpt
    ars -> App bodyOpt ars

foldBruijn n body args = let
  argSubs = V.fromList args
  in do
  when (V.length argSubs /= n) (error $ "unsaturated bruijn: args (" <> show (V.length argSubs) <> ") expected: " <> show n)
  bruijnArgs .= argSubs
  if n == 0 then pure body else simpleTerm body <* (bruijnArgs .= V.empty)

-- Constants | Labels
isSpecArg = \case { Label{}->True ; {- Match{}->True ; -} Var (VQBind{})->True ; Cons fs -> any isSpecArg fs ; _->False}

-- (do partial) β-reduction
simpleRecApp f argsRaw = simpleTerm f >>= \f' -> (simpleTerm `traverse` argsRaw) >>= simpleApp' True  f'
simpleApp    f argsRaw = simpleTerm f >>= \f' -> (simpleTerm `traverse` argsRaw) >>= simpleApp' False f'

-- One-step simpleApp that avoids simplifying its fn or args (unless β-reducing an Abs)
simpleApp' :: Bool -> Term -> [Term] -> SimplifierEnv s Term
simpleApp' isRec f args = (nApps %= (1+)) *> case f of
  App f2 args2 -> {-simpleTerm f2 >>= \f2' ->-} simpleApp' isRec f2 (args2 ++ args)
  BruijnAbs n free body -> foldBruijn n body args
  Abs argDefs free body ty -> foldAbs argDefs free body ty args
  Instr i -> pure $ simpleInstr i args
  Match retT branches d | [scrut] <- args -> fuseMatch retT scrut branches d
  fn -> let
    app f a = if isRec then RecApp f a else App f a
    hasSpecArgs = not (null args) && any isSpecArg args
    in case fn of
--  Abs argDefs' free body ty -> foldAbs argDefs' free body ty args
    Var (VBind i ) | hasSpecArgs -> use thisMod >>= \m -> mkSpecialisation (Left (mkQName m i)) args
    Var (VQBind q) | hasSpecArgs -> mkSpecialisation (Left q) args
    Spec i -> (specStack <<%= (`setBit` i)) >>= \sp -> use thisSpec >>= \this -> let
      testRec = when (this == i) (recSpecs %= (`setBit` i))
      in testRec *> use letSpecs >>= \ls -> use recSpecs >>= \recs -> if not (null args) && any isSpecArg args
        then mkSpecialisation (Right i) args -- can further specialise a specialisation (it was inlined and an arg became known)
        else MV.read ls i >>= \got -> case got of
          Just spec | not (sp `testBit` i || recs `testBit` i) -> simpleApp spec args -- Inlined a specialisation
          _   -> pure (app fn args)

    _ -> pure (app fn args)

-- Fusing Matches with constant labels is the main goal
fuseMatch :: Type -> Term -> BSM.BitSetMap Expr -> Maybe Expr -> SimplifierEnv s Term
fuseMatch ty scrut branches d = -- simpleTerm scrut' >>= \scrut ->
--((\(Core t ty) -> (`Core` ty) <$> simpleTerm t) `traverse` branchesRaw) >>= \branches -> let
  let this = App (Match ty branches d) [scrut]
  in case scrut of
  -- Ideal: case-of-label
  Label l params -> let getTerm (Just (Core t ty)) = t
--  in simpleApp' False (getTerm ((branches IM.!? qName2Key l) <|> d)) params
    in simpleApp (getTerm ((branches BSM.!? qName2Key l) <|> d)) params

  -- Near-Ideal: case-of-case: push outer case into each branch of the inner Case
  -- frequently the inner case can directly fuse with the outer cases output labels
  App (Match ty2 innerBranches innerDefault) [innerScrut] -> let
    pushCase (Core (Abs ars free body ty) _ty) = do
      branch <- simpleApp' False (Match ty branches d) [body]
      let newTy = case branch of { Abs _ _ _ t -> t ; _ -> tyBot } -- lost the Ty
      pure   (Core (Abs ars free branch newTy) newTy)
    in do
      optBranches <- innerBranches `forM` pushCase
      optD <- maybe (pure Nothing) (fmap Just . pushCase) d
      pure (App (Match ty2 optBranches optD) [innerScrut])

---- case-of-App: Hope to get a constant label after beta-reduction
-- TODO this may double simplify !
  App (Var (VQBind caseFnArg)) ars -> inline caseFnArg >>= \case
    Var{} -> pure this -- didn't manage to inline anything
    f -> simpleApp' False f ars >>= \scrutInline -> fuseMatch ty scrutInline branches d

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
