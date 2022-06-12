{-# LANGUAGE TypeFamilies , RecordWildCards #-}
module Mixfix (solveMixfixes) where
import Prelude hiding (sourceLine)
import MixfixSyn
import CoreSyn
import ShowCore()
import qualified Data.List as DL
import Text.Megaparsec
import Control.Monad (fail)

-- Temporary exprs for solveMixfixes
--data TMPExpr
-- = QVar     QName --(ModuleIName , IName)
-- | MFExpr   Mixfixy --MFWord -- removed by solvemixfixes
-- | ExprApp  Expr [Expr] -- output of solvemixfixes
-- | TMPExpr  Expr

-- megaparsec on custom stream : [Expr]
instance Eq Expr where (==) a b  = False
instance Ord Expr where (<=) a b = False
data JuxtStream = JuxtStream { unJuxtStream :: [Expr] }
instance Stream JuxtStream where
  type Token  JuxtStream = Expr
  type Tokens JuxtStream = [Expr]
  tokensToChunk Proxy x = x
  chunkToTokens Proxy   = identity
  chunkLength Proxy     = DL.length
  chunkEmpty Proxy      = null
  take1_ (JuxtStream s) = case s of { [] -> Nothing ; x : xs -> Just (x , JuxtStream xs) }
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
        { pstateInput  = JuxtStream postStr
        , pstateOffset = max pstateOffset o
        , pstateSourcePos = newSourcePos
        , pstateTabWidth = pstateTabWidth
        , pstateLinePrefix = prefix
        }
    )
    where
      prefix = pstateLinePrefix
      sameLine = sourceLine newSourcePos == sourceLine pstateSourcePos
      newSourcePos = pstateSourcePos
      (preStr, postStr) = splitAt tokensConsumed (unJuxtStream pstateInput)
      tokensConsumed = tokensConsumed
pxy = Proxy :: Proxy JuxtStream

-------------------
-- Mixfix Parser --
-------------------
type Parser = Parsec Void JuxtStream
prependArg a f = case f of { ExprApp f args -> ExprApp f (a:args) ; f -> ExprApp f [a] }
-- Also need to flip the arguments (since precedence swaps reverse apps)
appendArg  f a = case f of { ExprApp f args -> ExprApp f (a : reverse args) ; f -> ExprApp f [a] }
--mkApp :: [Expr] -> Expr
mkApp = \case { [a] -> a ; f:args -> ExprApp f args }
patchMFBind b = let
  patchQVar q = mkQName (modName q) b
  in \case
  QVar q -> QVar (patchQVar q)
  ExprApp (QVar q) args -> ExprApp (QVar (patchQVar q)) args

-- juxtappositions are ExprApps unless they contain mixfixes to extract and precedence solve
-- prec and assoc only matters for mf chains that both want the centre argument `m1_` `_m2`
-- general strategy is to parse postfix chains `startPostfix`; the only exception is if a juxt starts with a mixfixword
-- Complications arise when a name is both a mixfixword and a bindname by itself
solveMixfixes :: [Expr] -> Expr = let
  mfExpr = try anySingle >>= \case
    MFExpr mixfixy -> pure mixfixy
    e -> fail $ "expected a mixfixword: " <> show e
  getMFPart = \case { QMFPart i -> Just i ; _ -> Nothing }
  pMFWord qnm = try mfExpr >>= \(Mixfixy _maybeBind mfws) -> unless (qnm `elem` catMaybes (getMFPart <$> mfws)) (fail ("unexpected mfword: " <> show qnm))

  rawExpr = mkApp <$> takeWhile1P Nothing (\case {MFExpr{}->False ; _->True})
  arg = rawExpr <|> startPrefix

  -- parse expected mfwords (mfWs :: [Maybe IName])
  mfParts :: IName -> Maybe Expr -> QName -> Prec -> [Maybe IName] -> Parser Expr
  mfParts mb larg qNm fixity mfWs = let
    mkMFParser = \case -- figure out if the mixfix ends with a hole
      []           -> pure (False , [])
      [Nothing]    -> (\a -> (True , [a])) <$> arg
      Nothing : xs -> (\p (lastArg , l) -> (lastArg , p : l)) <$> expr <*> mkMFParser xs
      Just q  : xs -> (pMFWord q <|> fail ("expected mfword: " <> show q)) *> mkMFParser xs

--  in mkMFParser (fmap (fst qNm ,) <$> mfWs)
    in mkMFParser (fmap (mkQName (modName qNm)) <$> mfWs)
      <&> (\(pf,args) -> (pf , maybe (QVar qNm : args) (\la -> QVar qNm : la : args) larg))
      >>= \case -- did the mf end with _
       (False , p) -> pure   (patchMFBind mb (mkApp p)) -- end of mf train
       (True  , p) -> option (patchMFBind mb (mkApp p)) -- ends with '_' => parse more mfs
                      (try $ startPostfix (patchMFBind mb (mkApp p)) (Just (qNm , fixity)))

  startPostfix :: Expr -> (Maybe (QName , Prec)) -> Parser Expr
  startPostfix larg fixity = mfExpr >>= \(Mixfixy maybeBind mfWords) -> let
    mkPostfixParser (QStartPostfix (MixfixDef mb mfWs fixityR) qNmr) =
      let contMFWs = drop 2 mfWs -- _iden[...] (already parsed first hole and first iden)
      in case fixity of
      Just (qNml , fixityL) ->
        if qNml == qNmr && assoc fixityL == AssocNone
        then fail $ "operator not associative: " <> show qNml
        else if (qNml == qNmr && assoc fixityL /= AssocRight) || prec fixityL >= prec fixityR
        then (\x -> appendArg x larg) <$> mfParts mb Nothing qNmr fixityR contMFWs
        else case larg of -- `l_ _r` => r gets l's last arg, l gets all of r
          ExprApp f ars -> (\r -> ExprApp f (DL.init ars ++ [r]))
            <$> mfParts mb (Just (DL.last ars)) qNmr fixityR contMFWs
          _ -> error "impossible, fixity given for nonexistent left App"
      Nothing -> mfParts mb (Just larg) qNmr fixityR contMFWs
    mkPostfixParser _ = fail $ "not a postfix: " <> show mfWords
    in choice (try . mkPostfixParser <$> mfWords)
      <|> maybe (fail ("not a bindName: " <> show mfWords)) (\qvar -> mkApp . ([larg , QVar qvar ] ++) <$> many arg) maybeBind

  startPrefix = mfExpr >>= \(Mixfixy maybeBind mfWords) -> let
    mkPrefixParser = \case
      QStartPrefix (MixfixDef mb mfWs fixity) qNm -> mfParts mb Nothing qNm fixity (drop 1 mfWs)
      _ -> fail "not a prefix"
    in choice (try . mkPrefixParser <$> mfWords)
      <|> maybe (fail "not a bindName") (\qvar -> mkApp . (QVar qvar :) <$> many arg) maybeBind
  expr = arg >>= \a -> option a (try $ startPostfix a Nothing)
  in \s -> case runParser expr "<mixfix resolver>" (JuxtStream $ s) of
    Right r -> r
    Left e  -> error $ errorBundlePretty e
