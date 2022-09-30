module UnPattern (patternsToCase , matchesToTT) where
import Data.Functor.Foldable
import Data.Functor.Base
import ParseSyntax
import QName
import Builtins (builtinTrue , builtinFalse)
import qualified BitSetMap as BSM
import Control.Arrow
import qualified Data.List.NonEmpty as NE

-- Invert a TT into a case-tree, so mixfixes and labels are handled uniformly
-- Parse > resolve mixfixes > resolve cases > check arg scopes?
-- parse modules as Fn : [AllHNames] → Module (ie. structural parse , don't lookup anything since depends on mixfix parse)
-- codo on cofree comonad ⇒ DSL for case analysis on the base functor of the cofree comonad.

-- type Moore = Cofree (→ (Pattern , Rhs)) Scrut
-- Moore machine with states labeled with values of type Scrut, and transitions on edges of (Pattern , Rhs).

-- ? multi-arg case ⇒ arg inter-dependencies
-- ? pattern ⇔ case isomorphism for specialisations (need to operate on Term syntax)
-- β-optimality for sharing branches between different paps in dependency tree
-- [ [Pattern , TT] ] → [ Case ]        2 ^ (nArgs - 1) paps
-- case on tuples + labeled arg presence for β-optimality?

--eqnsToPatterns ∷ [[Term]] → [Term]
--eqnsToPatterns = map (Tuple . V.fromList)

type CasePattern = TT -- needs to be transformed into a case-tree
type Scrut   = TT
type MatchKO = Maybe BruijnAbs -- : Int → Term → LamB
type MatchOK = TT
type Rhs     = TT
type CaseAcc s = Scrut → MatchOK → MatchKO → {-ST s-} TT
-- TODO run in ST monad to update arg → bruijn map

-- λ (η a _) ⇒ \s0 → if λ s1 → if η s2 s3 → name s2 → rhs
-- Note. this assigns debruijn args to subPatterns
buildCase ∷ CasePattern → CaseAcc s
buildCase = let
--mkSubCases ∷ [CaseAcc s] → MatchOK → MatchKO → Rhs
  mkSubCases = let
    -- build a case where if any matches in the list fail , the whole list fails
    -- eg. [a , b] ⇒ (match a ⇒ match b ⇒ λa b ⇒ ok) else ko
--  subCaseF ∷ ListF CaseAcc (Int → MatchOK → MatchKO → Rhs) → Int → MatchOK → MatchKO → Rhs
    subCaseF ret bruijnI ok ko = let scrut = Var (VBruijn bruijnI)
      in case ret of
        Nil            → ok
        Cons caseAcc r → let
          nextMatch = r (bruijnI + 1) ok ko
          in caseAcc scrut nextMatch ko
    in \subPats → cata subCaseF subPats 0

  go ∷ TTF (CaseAcc s) → CaseAcc s -- Pass down a scrut and a default branch
  go pat scrut ok ko = case pat of
    LabelF q subPats → let
      branch = BruijnAbsF (length subPats) emptyBitSet (mkSubCases subPats ok ko) -- (η a b) ⇒ (\a b →)
      in MatchB scrut (BSM.singleton q branch) ko
    VarF _           → ok -- argument was named ⇒ need to sub it for its bruijn name !
    QuestionF        → ok -- unconditional match
    PatternGuardsF pats → mkSubCases pats ok ko
    ArgProdF cc      → mkSubCases cc ok ko
    ProdF cc         → let
      c = BSM.fromList cc -- TODO
      n = BSM.size c
      (keys , subPats) = unzip (BSM.toList c)
      unConsArgs = keys <&> \k → TTLens 0 scrut [k] LensGet
      body = mkSubCases subPats ok ko
      in App (BruijnLam (BruijnAbsF n emptyBitSet body)) unConsArgs
    LitF l          → let
      alts = (qName2Key builtinTrue , BruijnAbsF 1 emptyBitSet ok)
        : maybe [] (\falseBranch → [(qName2Key builtinFalse , falseBranch)]) ko
      in MatchB (LitEq l scrut) (BSM.fromList alts) Nothing
    x → DesugarPoison $ "Illegal pattern: " <> show (embed $ x <&> (\x → x scrut ok ko))
  in cata go -- scrut matchOK matchKO → Term

patternsToCase ∷ Scrut → [(CasePattern , Rhs)] → Rhs
patternsToCase scrut patBranchPairs = let
  matches ∷ [Rhs]
  matches = patBranchPairs <&> \(pat , rhs) → buildCase pat scrut rhs Nothing

  mergeCasesF ∷ NonEmptyF TT TT → TT
  mergeCasesF (NonEmptyF r Nothing) = r
  mergeCasesF (NonEmptyF case1 (Just case2)) = case (case1 , case2) of
    (MatchB s1 b1 ko1 , MatchB s2 b2 ko2) {-| s1 == s2-}
      → MatchB s1 (BSM.unionWith (\_ _ → BruijnAbsF 0 emptyBitSet (DesugarPoison "redundant pattern match")) b1 b2) ko2 -- second one wins
    _ → DesugarPoison $ "cannot merge cases: " <> show case1 <> " ↔ " <> show case2
  in case matches of
    []       → DesugarPoison "EmptyCase"
    (x : xs) → cata mergeCasesF (x :| xs)

matchesToTT ∷ NonEmpty FnMatch → BruijnAbs
matchesToTT ms = let
  argCount = NE.head ms & \(FnMatch pats _) → length pats -- mergeCasesF will notice if there is a discrepancy in arg counts
  rhs = patternsToCase Question $ toList (ms <&> \(FnMatch pats rhs) → (ArgProd pats , rhs))
  in BruijnAbsF argCount emptyBitSet rhs
