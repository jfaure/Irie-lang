{-# LANGUAGE TypeFamilies , RecordWildCards #-}
module Mixfix (solveMixfixes) where
import Prelude hiding (sourceLine)
import MixfixSyn
import CoreSyn
import ShowCore()
import qualified Data.List as DL -- ( length, init, last, span )
import Text.Megaparsec
import Control.Monad (fail)

-- Temporary exprs for solveMixfixes
--data TMPExpr
-- = QVar     QName --(ModuleIName , IName)
-- | MFExpr   Mixfixy --MFWord -- removed by solvemixfixes
-- | ExprApp  Expr [Expr] -- output of solvemixfixes
-- | TMPExpr  Expr

-- megaparsec on custom stream : [Expr]
instance Eq Expr where (==) _a _b  = False
instance Ord Expr where (<=) _a _b = False
data JuxtStream = JuxtStream { unJuxtStream ∷ [Expr] }
instance Stream JuxtStream where
  type Token  JuxtStream = Expr
  type Tokens JuxtStream = [Expr]
  tokensToChunk Proxy x = x
  chunkToTokens Proxy   = identity
  chunkLength Proxy     = DL.length
  chunkEmpty Proxy      = null
  take1_ (JuxtStream s) = case s of { [] → Nothing ; x : xs → Just (x , JuxtStream xs) }
  takeN_ n (JuxtStream s)
    | n <= 0    = Just ([] , JuxtStream s)
    | null s    = Nothing
    | otherwise = let (x , s') = splitAt n s in Just (x , JuxtStream s')
  takeWhile_ f (JuxtStream s) = let (x , s') = DL.span f s in (x , JuxtStream s')
instance VisualStream JuxtStream where
  showTokens Proxy = intercalate " " . toList . fmap (show)
  tokensLength Proxy xs = length xs -- sum (tokenLength <$> xs)
instance TraversableStream JuxtStream where
  reachOffset o PosState {..} =
    ( Just prefix
    , PosState
        { pstateInput      = JuxtStream postStr
        , pstateOffset     = max pstateOffset o
        , pstateSourcePos  = newSourcePos
        , pstateTabWidth   = pstateTabWidth
        , pstateLinePrefix = prefix
        }
    )
    where
      prefix = pstateLinePrefix
--    sameLine = sourceLine newSourcePos == sourceLine pstateSourcePos
      newSourcePos = pstateSourcePos
      (_preStr, postStr) = splitAt tokensConsumed (unJuxtStream pstateInput)
      tokensConsumed = tokensConsumed

-------------------
-- Mixfix Parser --
-------------------
type Parser = Parsec Void JuxtStream
-- Solves a different problem than makeExpressionParser, since the fixities must be read from the mixfixes as they are parsed
solveMixfixes ∷ [Expr] → Expr = let
  goMF ∷ Expr → MixfixDef → QName → Parser Expr
  goMF prev (MixfixDef mb mfWords fixityL) qNml = {-d_ (prev , mfWords , qNml) $-} let
    modNm = modName qNml
    getMFPart = \case { QMFPart i → Just i ; _ → Nothing }
    pMFWord qnm = satisfy (\case { MFExpr (Mixfixy _ mfws) → qnm `elem` catMaybes (getMFPart <$> mfws) ; _ → False})
    pMFWords ∷ [Maybe IName] → Parser (Maybe (MixfixDef, QName), [Expr])
    pMFWords = \case
      []           → pure (Nothing , [])
      -- `if 1 then 5 + 1 else 0` _+_ will try to eat the 'else'
      [Nothing]    → try (pExpr False ≫= \f → option (Nothing , [f]) $ pPostFix (Just (fixityL , qNml)) f)
        <|> (\e → (Nothing , [e])) <$> simpleExpr
      Nothing : xs → (\a (m,ars) → (m , a : ars)) <$> pExpr True <*> pMFWords xs
      Just i  : xs → pMFWord (mkQName modNm i) *> pMFWords xs -- TODO use right modNm
    end (m , ars) = let patchQName mb q = mkQName (modName q) mb -- replace mixfix word QName with it's QBind
      in case m of
      Just (md , qNmr) → goMF (ExprApp (QVar $ patchQName mb qNml) (prev : ars)) md qNmr -- l won, wrap it and parse more args for r
      Nothing          → pure (ExprApp (QVar $ patchQName mb qNml) (prev : ars)) -- l lost, it gets the r expr as an arg
    in pMFWords mfWords ≫= end

  -- Everything revolves around the pattern `if_then_else_ ARG _*_` , where 2 mixfixes fight for the same arg
  pPostFix ∷ Maybe (Prec , QName) → Expr → Parser (Maybe (MixfixDef , QName) , [Expr])
  pPostFix mqNml midArg = satisfy ((\case {MFExpr{}→True ; _→False})) ≫= \(MFExpr (Mixfixy q qs)) → choice $ qs <&> \case
    (QStartPostfix (MixfixDef mb mfWs fixityR) qNmr) → let
      md = MixfixDef mb (drop 2 mfWs) fixityR
      in case mqNml of
      Nothing → (\r → (Nothing , [r])) <$> goMF midArg md qNmr -- no left mixfix to fight with
      Just (fixityL , qNml) →
        if qNml == qNmr && assoc fixityL == AssocNone then fail $ "operator not associative: " <> show qNml
        else if prec fixityL > prec fixityR || (qNml == qNmr && assoc fixityL /= AssocRight) -- l wins ?
        then pure (Just (md , qNmr) , [midArg]) -- l wins midArg, r needs to wrap up l before parsing more mfs from the top
        else (\r → (Nothing , [r])) <$> goMF midArg md qNmr -- r wins midArg, can continue parsing
    x → fail $ "not a postfix start: " <> show x

  args  = takeWhile1P Nothing (\case {MFExpr{}→False ; _→True})
  simpleExpr = args <&> \case { [f] → f ; f : ars → ExprApp f ars ; _ → _ }

  pExpr ∷ Bool → Parser Expr
  pExpr doPostFix = anySingle ≫= \case
    MFExpr (Mixfixy _q qmfs) → pExpr True ≫= \larg → choice $ qmfs <&> \case
      QStartPrefix (MixfixDef mb mfws fixityR) qNmr → try $ goMF larg (MixfixDef mb (drop 2 mfws) fixityR) qNmr
      _ → fail "not prefix"
    f → option f (ExprApp f <$> args) ≫= \larg → if doPostFix
      then option larg $ try $ pPostFix Nothing larg <&> \(Nothing , [v]) → v else pure larg
  in \s → either ((error $!) . traceShowId . errorBundlePretty) identity (runParser (pExpr True) "<mixfix resolver>" (JuxtStream s))
