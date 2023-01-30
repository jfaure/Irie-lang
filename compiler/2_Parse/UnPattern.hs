module UnPattern (patternsToCase , Scrut) where
import Data.Functor.Foldable
import Data.Functor.Base
import ParseSyntax
import QName
import Builtins (builtinTrueQ , builtinFalseQ)
import qualified BitSetMap as BSM
import qualified Data.List.NonEmpty as NE

-- Invert a TT into a case-tree, so mixfixes and labels are handled uniformly
-- Parse > resolve mixfixes > resolve cases > check arg scopes?
-- parse modules as Fn : [AllHNames] -> Module (ie. structural parse , don't lookup anything since depends on mixfix parse)
-- codo on cofree comonad => DSL for case analysis on the base functor of the cofree comonad.

-- ? multi-arg case ⇒ arg inter-dependencies
-- ? pattern <=> case isomorphism for specialisations (need to operate on Term syntax)
-- β-optimality for sharing branches between different paps in dependency tree
-- [ [Pattern , TT] ] -> [ Case ]        2 ^ (nArgs - 1) paps
-- case on tuples + labeled arg presence for β-optimality?

--eqnsToPatterns ∷ [[Term]] -> [Term]
--eqnsToPatterns = map (Tuple . V.fromList)

type CasePattern = TT -- needs to be transformed into a case-tree
type Scrut   = TT
type MatchKO = Maybe TT -- BruijnAbs -- : Int -> Term -> LamB
type MatchOK = TT
type Rhs     = TT
type Bruijns = Int
type CaseAcc = Scrut -> Bruijns -> MatchOK -> MatchKO -> (TT , BruijnSubs)

-- λ (η a _) => \s0 -> if λ s1 -> if η s2 s3 -> name s2 -> rhs
-- Note. this assigns debruijn args to subPatterns which must be mapped from VExterns later
-- bN is number of enclosing deBruijns, since these must be incremented as they are passed down
buildCase :: CasePattern -> CaseAcc
buildCase = let
  mkSubCases :: [CaseAcc] -> Bruijns -> Int -> MatchOK -> MatchKO -> (Rhs , BruijnSubs)
  -- bN = bruijn acc , n = current lambda abstraction
  mkSubCases subPats bN n ok ko = let
    -- build a case where if any matches in the list fail , the whole list fails
    -- eg. [a , b] => (match a => match b => λa b => ok) else ko
    subCaseF :: Int -> ListF CaseAcc (Int -> MatchOK -> MatchKO -> (Rhs , [(IName , Int)]))
                                   -> Int -> MatchOK -> MatchKO -> (Rhs , [(IName , Int)])
    subCaseF subN ret bruijnI ok ko = case ret of
      Nil            -> (ok , [])
      Cons caseAcc r -> let
        (nextMatch , argSubs) = r (bruijnI + 1) ok ko
        scrut = Var (VBruijn bruijnI)
        (this , argSubs2) = caseAcc scrut subN nextMatch ko
        -- TODO need to obtain the new debruijnN introduced by subcases !
        in (this , argSubs2 ++ argSubs)
    in cata (subCaseF (bN + n)) subPats bN ok ko

  go :: TTF CaseAcc -> CaseAcc -- Pass down a scrut and a default branch
  go pat scrut bN ok ko = {-d_ (embed $ Question <$ pat) $-} let
    noSubs = (,[])
    goLabel q subPats = let
      n = length subPats
      (rhs , argSubs) = mkSubCases subPats bN n ok ko
      branch = mkBruijnLam (BruijnAbsF n argSubs 0 rhs) -- (η a b) => (\a b ->)
      in noSubs $ MatchB scrut (BSM.singleton q branch) ko
    in case pat of
    LabelF q subPats  -> goLabel q subPats -- argument was named => need to sub it for its bruijn name !
    AppExtF q subPats -> goLabel q subPats
    VarF (VExtern i) -> case scrut of
      Var (VBruijn b) -> (ok , [(i , b)])
      _ -> (DesugarPoison ("Unknown label: " <> show i) , [])
    VarF _              -> noSubs ok
    QuestionF           -> noSubs ok -- unconditional match
    PatternGuardsF pats -> mkSubCases pats bN 0 ok ko
    ArgProdF caseAcc    -> let (this , bruijnSubs) = caseAcc (Var (VBruijn bN)) (bN + 1) ok ko
      in (mkBruijnLam (BruijnAbsF 1 bruijnSubs 0 this) , [])
--  ArgProdF cc    -> let n = length cc in mkSubCases cc bN n ok ko & \(rhs , bruijnSubs) ->
--    (mkBruijnLam (BruijnAbsF n bruijnSubs 0 rhs) , [])
    TupleF subPats -> let -- (DesugarPoison "Unprepared for tuple" , [])
      n = length subPats 
      unConsArgs = [qName2Key (mkQName 0 i) | i <- [0 .. n-1]] <&> \k -> TTLens (-1) scrut [k] LensGet
      (body , argSubs) = mkSubCases subPats bN n ok ko
      in (App (mkBruijnLam (BruijnAbsF n argSubs 0 body)) unConsArgs , argSubs)
    LitF l          -> noSubs $ let
      alts = (qName2Key builtinTrueQ , BruijnLam $ BruijnAbsF 1 [] 0 ok)
        : maybe [] (\falseBranch -> [(qName2Key builtinFalseQ , falseBranch)]) ko
      in MatchB (LitEq l scrut) (BSM.fromList alts) Nothing
    x -> noSubs $ DesugarPoison ("Illegal pattern: " <> show (embed $ x <&> (\x -> fst $ x scrut bN ok ko)))
  in cata go -- scrut matchOK matchKO -> Term

patternsToCase :: Scrut -> Int -> [(CasePattern , Rhs)] -> (Rhs , BruijnSubs)
patternsToCase scrut bruijnAcc patBranchPairs = let
  r :: ([Rhs] , [BruijnSubs])
  r@(matches , bruijnSubs) = unzip $ patBranchPairs <&> \(pat , rhs) -> buildCase pat scrut bruijnAcc rhs Nothing

  mergeCasesF :: NonEmptyF TT TT -> TT
  mergeCasesF (NonEmptyF r Nothing) = r
  mergeCasesF (NonEmptyF case1 (Just case2)) = case (case1 , case2) of
    (MatchB s1 b1 ko1 , MatchB s2 b2 ko2) {- | s1 == s2-}
      -> let mergeBranches a b = DesugarPoison $ "redundant pattern match: " <> show a <> show b
         in MatchB s1 (BSM.unionWith mergeBranches b1 b2) ko2 -- second one wins
    _ -> DesugarPoison $ "cannot merge cases " <> show scrut <> " of "<> show case1 <> " <=> " <> show case2
  in (, concat bruijnSubs) $ case matches of
    []     -> DesugarPoison "EmptyCase"
    x : xs -> cata mergeCasesF (x :| xs)
