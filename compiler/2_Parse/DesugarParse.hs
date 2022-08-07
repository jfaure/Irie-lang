module DesugarParse (matches2TT , patterns2TT) where
import Prim
import ParseSyntax
import CoreSyn (Term(Instr))
import Data.List (findIndex)

type FnArg = (IName , Maybe TT) -- arg and maybe type sig
type Body  = TT

matches2TT ∷ NonEmpty FnMatch → ([FnArg] , Body)
matches2TT matches = foldl1 addCase ((\(FnMatch pats e) → patterns2TT pats e) <$> matches)

-- acc is a Case tree on the arguments
-- It's up to the simplifier to try improve the case tree later
addCase ∷ ([FnArg] , Body) → ([FnArg] , Body) → ([FnArg] , Body)
addCase (accArgs , acc) (nextArgs , nextAcc) = let
  -- join equations by substituting arg names (this indirection allows users to name the same arg differently in each match)
  subArgs newArgs body = let
    mkTypedPat (i , t) = maybe (PArg i) (PTyped i) t
    abs = Abs (FnDef "argSub" Let Nothing 0 (FnMatch (mkTypedPat <$> newArgs) body :| []) Nothing)
    -- ! only necessary if AsPattern or not a composite
    in App abs (Var . VLocal . fst <$> accArgs)
  in case acc of
  -- Need to merge cases when possible
  App (Match ls Nothing) [Var (VLocal arg1)] → case nextAcc of
    App (Match l2s d) [Var (VLocal arg2)] | findIndex ((==arg1) . fst) accArgs == findIndex ((==arg2) . fst) nextArgs → let
      patchedL2s = fmap (subArgs nextArgs) <$> l2s
      in (accArgs , App (Match (ls ++ patchedL2s) d) [Var (VLocal arg1)])
    _ → (accArgs , Match ls (Just $ subArgs nextArgs nextAcc))
  tt → d_ ("redundant Pattern match: " <> show nextAcc ∷ Text) (accArgs , tt) -- we are already matching unconditionally..

-- The Maybe function returned by convPat serves to convert nested Pattern Apps into nested cases
patterns2TT ∷ [Pattern] → Body → ([FnArg] , Body)
patterns2TT pats e = let
  (argAndTys , e') = unzip $ convPat <$> pats
  e'' = foldl (\b → maybe b ($ b)) e e'
  in (argAndTys , e'')

-- Return the Argument INames, with their Maybe type signatures, and the body for the fnMatch
convPat ∷ Pattern → (FnArg , Maybe (TT → TT))
convPat = \case
  PArg  i     → ((i , Nothing) , Nothing)
  PPi (PiBound [i] ty) → ((i , Just ty) , Nothing)
  PTyped i ty → ((i , Just ty) , Nothing)

  PComp i pat → ((i , Nothing) ,) . Just $ let
    thisArg = Var (VLocal i) --(if isTop then VBind i else VLocal i)
    -- t is the term returned by this case expression
    in \t → case pat of
    PWildCard      → t -- pcomp names the arg but it's never used
    PLabel l pats  → App (Match [(l , emptyBitSet , pats , t)] Nothing) [thisArg]
    PLit lit       → _ -- LitEq lit thisArg t
    PTuple  fields → let
    -- Note the convention that negative numbers indicate tuple indexing
      mkProj l (PArg i) = (i , TTLens 0 thisArg [l] LensGet) -- (i , Idx thisArg l)
      mkProj _ p = error $ "not ready for patterns within tuples: " <> show p
      (fieldArgs , projs) = unzip $ zipWith mkProj [-1,-2..] fields
      fArgs = PArg <$> fieldArgs
      abs = Abs (FnDef "tupleProj" Let Nothing 0 (FnMatch fArgs t :| []) Nothing)
      in App abs projs
    PCons  fields → let
      mkProj (l , PArg i) = (i , TTLens 0 thisArg [l] LensGet)
      mkProj p = error $ "not ready for patterns within records" <> show p
      (fieldArgs , projs) = unzip $ mkProj <$> fields
      fArgs = PArg <$> fieldArgs
      abs  = Abs (FnDef "patProj" Let Nothing 0 (FnMatch fArgs t :| []) Nothing)
      in App abs projs
--  x → error $ "not ready for pattern: " <> show x
  x → error $ "unknown pattern: " <> show x
