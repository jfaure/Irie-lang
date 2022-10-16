module Parser (parseModule , parseMixFixDef) where
import Prim ( Literal(PolyFrac, Char, String, Int, PolyInt) )
import ParseSyntax as P
import MixfixSyn ( defaultPrec, Assoc(..), MFWord(..), MixfixDef(..), Prec(Prec) )
import UnPattern (matchesToTT)
import Text.Megaparsec
import Text.Megaparsec.Char ( char, char', string )
import qualified Data.Vector as V
import System.FilePath.Posix as FilePath (dropExtension , takeFileName)
import qualified Text.Megaparsec.Char.Lexer as L ( binary, charLiteral, hexadecimal, octal, skipLineComment, space, symbol, decimal, indentLevel, lexeme )
import Control.Monad (fail)
import Control.Lens
import qualified Data.Map.Strict as M
import qualified Data.Set as S ( fromList, member )
import qualified Data.Text as T ( all, any, append, concat, null, snoc, empty )
import MUnrolls
import Data.Functor.Foldable
import Control.Arrow
--import qualified Text.Megaparsec.Debug as DBG

-- The initial parse is context-insensitive: forward | mutual definitions and mixfixes are resolved later
-- Parsing converts all text names to INames (Int) and doesn't depend on imports

-- debug fns
-- dbg i = DBG.dbg i
-- showN n = try ((takeP Nothing n >>= traceShowM) *> fail "debug parser") <|> pure () :: Parser ()

type Parser = ParsecT Void Text (Prelude.State ParseState)

--------------------------
-- Parsestate functions --
--------------------------
addImport i   = moduleWIP . imports  %= (i:)
addMFWord h mfw = do
  sz <- moduleWIP . parseDetails . hNameMFWords . _1 <<%= (+1)
  moduleWIP . parseDetails . hNameMFWords . _2 %= M.insertWith (++) h [mfw sz]
  pure sz

-- insertLookup is tricky but saves a log(n) operation
insertOrRetrieve :: HName -> Map HName Int -> (Either Int Int, Map HName Int)
insertOrRetrieve h mp = let sz = M.size mp in case M.insertLookupWithKey (\_k _new old -> old) h sz mp of
  (Just x , mp) -> (Right x  , mp)
  (_      , mp) -> (Left  sz , mp)

addBindName h    = (identity ||| identity) <$> (moduleWIP . parseDetails . hNameBinds %%= insertOrRetrieve h)
addUnknownName h = (identity ||| identity) <$> (moduleWIP . parseDetails . hNamesNoScope %%= insertOrRetrieve h)
newFLabel h      = (identity ||| identity) <$> (moduleWIP . parseDetails . fields %%= insertOrRetrieve h)
newSLabel h      = (identity ||| identity) <$> (moduleWIP . parseDetails . labels %%= insertOrRetrieve h)

lookupSLabel h   = (M.!? h) <$> use (moduleWIP . parseDetails . labels)
lookupBindName h = Var . VExtern <$> addUnknownName h

-----------
-- Lexer --
-----------
-- A key convention: tokens consume trailing whitespace (using `symbol` or `lexeme`)
-- so parsers can assume they start on a non-blank.
-- Space consumers: scn eats newlines, sc does not.
-- Save newline offsets so we can track source locations using a single Int
addNewlineOffset :: Parser ()
addNewlineOffset = getOffset >>= \o -> moduleWIP . parseDetails . newLines %= (o - 1 :)
isHSpace x = isSpace x && x /= '\n' && x /= '\t' -- isHSpace , but handles all unicode spaces
tabsc :: Parser () = L.space (void $ takeWhile1P (Just "tabs") (== '\t')) lineComment blockComment
-- TODO sc shouldn't eat tabs?
sc  :: Parser () = L.space (void $ takeWhile1P (Just "white space") isHSpace) lineComment blockComment
scn :: Parser () = let
  space1 = sc *> some endLine *> skipMany (sc *> endLine)
  in L.space space1 lineComment blockComment
scnTabs :: Parser () = let
  space1 = sc *> some endLine *> skipMany (tabsc *> endLine)
  in L.space space1 lineComment blockComment

endLine = lexeme (single '\n') <* addNewlineOffset
lineComment = L.skipLineComment "--" -- <* addNewlineOffset
blockComment = let -- still need to count newlines
  skipBlockComment start end = string start
    *> manyTill (endLine {-<|> blockComment nested-} <|> anySingle) end
  in void $ skipBlockComment "{-" "-}" <|> skipBlockComment "(*" "*)"

lexeme, lexemen :: Parser a -> Parser a -- parser then whitespace
lexeme  = L.lexeme sc
lexemen = L.lexeme scn
symbol :: Text -> Parser Text --verbatim strings
symbol = L.symbol sc

parens, braces, brackets :: Parser a -> Parser a
parens    = symbol  "(" `between` symbol  ")"
braces    = symbol  "{" `between` symbol  "}"
brackets  = symbol  "[" `between` symbol  "]"

-- ref = reference indent level
-- lvl = lvl of first indented item (often == pos)
indentedItems :: Pos -> Parser a -> Parser () -> Parser [a]
indentedItems prev p finished = let
 go lvl = indentn *> do
  pos <- L.indentLevel
--svIndent
  [] <$ lookAhead (eof <|> finished) <|> if
  -- 'fail' here backtracks the whitespace/newlines. Otherwise the App parser sees and eats things from later lines
    | pos <= prev -> fail ("end of indent: " <> show pos <> " <= " <> show prev)
    | pos == lvl  -> p >>= \ok -> option [ok] ((ok :) <$> try (go lvl))
    | otherwise   -> fail ("incorrect indentation, got " <> show pos <> ", expected " <> show lvl <> " (<= " <> show prev <>")")
 in L.indentLevel >>= go

indentn = use indentType >>= \case
  IndentTab    -> scnTabs
  IndentSpace  -> scn
  IndentEither -> scnTabs <* (indentType .= IndentTab) <|> scn <* (indentType .= IndentSpace)

-- tells linefold and let-ins not to eat our indentedItems
svIndent = L.indentLevel >>= (indent <.=)

linefold p = endLine *> scn *> do
  prev <- use indent
  cur  <- svIndent
  when (cur <= prev) (fail $ "not a linefold " <> show prev <> ", expected >= " <> show cur)
  p

-----------
-- Names --
-----------
reservedChars = ".@(){};:,\\\""
reservedNames = S.fromList $ words "let rec in \\case λcase case as over foreign foreignVarArg where of _ import use open require = ? | λ => ⇒"
-- check the name isn't an iden which starts with a reservedWord
reservedName w = (void . lexeme . try) (string w *> notFollowedBy idenChars)
reservedChar c = if T.any (==c) reservedChars then lexeme (char c) else lexeme (char c <* notFollowedBy idenChars)
reservedOp = reservedName
reserved = reservedName
isIdenChar x = not (isSpace x || T.any (==x) reservedChars)
idenChars = takeWhile1P Nothing isIdenChar
checkReserved x = x <$ when (x `S.member` reservedNames) (fail ("keyword '" <> toS x <> "' cannot be an identifier"))
checkLiteral x  = x <$ when (isDigit `T.all` x) -- TODO not good enough (1e3 , 2.0 etc..)
  (fail ("literal: '" <> toS x <> "' cannot be an identifier"))
checkIden = checkReserved <=< checkLiteral

-- We must use 'try', to backtrack if we ended up parsing a reserved word
iden :: Parser HName = lexeme . try $ (idenChars >>= checkIden)
idenNo_ = lexeme idenNo_'
idenNo_' = try (takeWhile1P Nothing (\x->isIdenChar x && x /= '_') >>= checkIden)

-- separated and split on '_' (ie. argument holes)
pMixfixWords :: Parser [Maybe Text] = lexeme $ do
  some (choice [Nothing <$ char '_' , Just <$> idenNo_']) >>= \case
    [Nothing] -> fail "'_' cannot be an identifier"
    mf -> pure mf

-- exported convenience function for use by builtins (Externs.hs)
parseMixFixDef :: Text -> Either (ParseErrorBundle Text Void) [Maybe Text]
 = \t -> runParserT pMixfixWords "<internal>" t `evalState` emptyParseState "dummy"

------------
-- Parser --
------------
parseModule :: FilePath -> Text -> Either (ParseErrorBundle Text Void) Module
parseModule nm txt = let
--parseModule = scn *> (parseDecls (mkPos 1) >>= (moduleWIP . bindings .=)) *> eof *> use moduleWIP
  parseModule = scn *> (((\binds -> LetIn binds Nothing) <$> pBlock Let)
    >>= (moduleWIP . bindings .=)) *> eof *> use moduleWIP
  in runParserT parseModule nm txt `evalState` emptyParseState (toS (dropExtension (takeFileName nm)))

mixFix2Nm = T.concat . map (\case { Just nm->nm ; Nothing->"_" })
parsePrec = let
  assoc = choice [Assoc <$ single 'a' , AssocRight <$ single 'r' , AssocLeft <$ single 'l' , AssocNone <$ single 'n']
  in lexeme $ Prec
  <$> (assoc     <?> "assoc : [a | l | r | n]")
  <*> (L.decimal <?> "precedence (an integer)")

addMixfixWords :: [Maybe HName] -> MixfixDef -> Parser [Maybe Int]
addMixfixWords m mfdef = let
  addMFParts mfp = traverse (traverse (`addMFWord` MFPart)) mfp
  in case m of
    Just hNm           : mfp -> addMFWord hNm (StartPrefix mfdef)
      >>= \w -> (Just w : )              <$> addMFParts mfp
    Nothing : Just hNm : mfp -> addMFWord hNm (StartPostfix mfdef)
      >>= \w -> (Nothing :) . (Just w :) <$> addMFParts mfp
    _ -> fail "panic: internal parse error with mixfixes"

pImport = choice
 [ reserved "import" *> (iden >>= addImport)
 , reserved "open"   *> (iden >>= addImport)
 , reserved "use"    *> (iden >>= addImport)
 ]

newtype SubParser = SubParser { unSubParser :: Parser (Maybe (FnDef , SubParser)) }
parseDecls :: Pos -> Parser (V.Vector FnDef)
parseDecls indent = V.unfoldrM unSubParser (pDecl indent)
pDecl :: Pos -> SubParser
pDecl indent = SubParser $ (<* (optional endLine <* scn)) $ (many (lexemen pImport) *> svIndent) *> let
  -- parse a name but consume all idenChars; ie. if expecting "take", don't parse "takeWhile" 
  pName nm = symbol nm *> lookAhead (satisfy (not . isIdenChar))
  pEqns :: Parser [TT] -> Parser [TT] -> Parser [(TT , TT)]
  pEqns pArgs pMFArgs = let -- first parse is possibly different
    fnMatch :: Parser [TT] -> Parser () -> Parser (TT , TT)
    fnMatch pMFArgs sep = (,) <$> (ArgProd <$> pMFArgs) <* lexemen sep <*> tt
    in -- optional tyAnn >>= \_ann -> -- TODO maybe don't allow `_+_ a b = add a b`
      (:) <$> fnMatch pArgs (reserved "=")
          <*> many (try $ endLine *> scn *> svIndent *> fnMatch pMFArgs (reserved "="))
      <|> some (try (endLine *> fnMatch pMFArgs (reserved "=")))
  in option Nothing $ optional (reserved "rec") *> lexeme pMixfixWords >>= \case
    [Just nm] -> let pArgs = many (lexeme singlePattern) in do
      iNm  <- addUnknownName nm <* addBindName nm
      eqns <- pEqns pArgs (pName nm *> pArgs)
      let rhs = CasePat $ CaseSplits (Var (VBruijn 0)) eqns
      pure $ Just (FnDef nm iNm Let Nothing rhs Nothing , pDecl indent)
    mfDefHNames   -> let
      pMixFixArgs = cata $ \case
        Nil      -> pure []
        Cons m x -> maybe ((:) <$> lexeme singlePattern <*> x) (\nm -> pName nm *> x) m
      nm = mixFix2Nm mfDefHNames
      in mdo -- for mfdef
      let mfDef = MixfixDef iNm mfDefINames prec
      iNm  <- addUnknownName nm <* addBindName nm
      prec <- fromMaybe defaultPrec <$> optional (braces parsePrec)
      mfDefINames <- addMixfixWords mfDefHNames mfDef
      rhs <- CasePat . CaseSplits (Var (VBruijn 0)) <$> pEqns (pure []) (pMixFixArgs mfDefHNames)
      pure $ Just (FnDef nm iNm Let (Just mfDef) rhs Nothing , pDecl indent)

lambda = matchesToTT <$> (:|[]) <$> fnMatch (many singlePattern) (reserved "=>" <|> reserved "⇒" <|> reserved "=")
tyAnn = reservedChar ':' *> tt 

fnMatch pMFArgs sep = FnMatch <$> pMFArgs <* lexemen sep <*> tt

-- make a lambda around any '_' found within the tt eg. `(_ + 1)` ⇒ `\x ⇒ x + 1`
catchUnderscoreAbs = pure

singlePattern = ttArg -- pattern TTs are inversed later
tt :: Parser TT
(tt , ttArg) = (anyTT , arg) where
  anyTT = ({-tySum <|>-} appOrArg) >>= catchUnderscoreAbs >>= typedTT <?> "tt"
   -- lens '.' binds tighter than App
  argOrLens = arg >>= \larg -> option larg (lens larg)
  lineFoldArgs p = let
    oneLineFold = (:) <$> try (linefold p) <*> many p <* lookAhead (single '\n')
    in choice [ oneLineFold , (:) <$> p <*> lineFoldArgs p , pure [] ]
      >>= \ars -> option ars ((ars ++) <$> oneLineFold)
  appOrArg  = getOffset >>= \o -> argOrLens >>= \larg -> option larg $ case larg of
--  Lit l -> LitArray . (l:) <$> some (lexeme $ try (literalP <* notFollowedBy iden)) -- Breaks `5 + 5`
    P.Label l [] -> P.Label l <$> lineFoldArgs argOrLens
    fn     -> (\args -> if null args then fn else Juxt o (fn : args)) <$> lineFoldArgs argOrLens
  lens :: TT -> Parser TT
  lens record = let
    lensNext path = reservedChar '.' *> getOffset >>= \o -> choice [
        TTLens o record (reverse path) <$> (LensSet  <$ reserved "set"  <*> argOrLens)
      , TTLens o record (reverse path) <$> (LensOver <$ reserved "over" <*> argOrLens)
      , idenNo_ >>= newFLabel >>= \p -> choice [lensNext (p : path) , pure (TTLens o record (reverse (p:path)) LensGet)]
      ]
    in lensNext []
  arg = choice
   [ reserved "?" $> Question
   , reserved "_" $> WildCard
   , letIn
   , (reserved "\\case" <|> reserved "λcase") *> lambdaCase
   , (reservedChar '\\' <|> reservedChar 'λ') *> lambda
-- , reserved "do" *> doExpr
   , reserved "case"   *> casePat
   , reserved "record" *> tyRecord  -- multiline record decl
   , reserved "data"   *> tySumData -- multiline sumdata decl
   , con
   , Lit <$> lexeme (try (literalP <* notFollowedBy iden)) -- must be before Iden parsers
   , reservedChar '@' *> idenNo_ >>= newSLabel <&> \l -> P.Label l []
   , try $ idenNo_ >>= \x -> choice [label x , lookupBindName x]
   , try $ iden >>= lookupBindName -- holey names used as defined
   , TyListOf <$> brackets tt
   , parensExpr
   , P.List <$> brackets (tt `sepBy` reservedChar ',' <|> (scn $> []))
   ] <?> "ttArg"

--piBinder = reserved "Π" *> (many (iden >>= addArgName) >>= \pis -> addPiBound (PiBound pis WildCard))
  -- Catch potential implicit abstractions at each parens
--parensExpr = parens (choice [{-try piBound ,-} (tt >>= \t -> tuple t <|> typedTT t) , scn $> Prod []] >>= implicitPiBound) >>= catchUnderscoreAbs
  parensExpr = parens ((tt >>= \t -> tuple t <|> typedTT t) <|> scn $> Prod [])
    >>= catchUnderscoreAbs
  tuple t = (\ts -> Tuple (t:ts)) <$> some (reservedChar ',' *> arg)
  label i = lookupSLabel i >>= \case
    Nothing -> P.Label <$ reserved "@" <*> newSLabel i <*> many arg
    Just l  -> pure $ P.Label l [] -- <$> many arg (converted in App)

  tySumData = Gadt <$> do
    let labelDecl = (,,) <$> (iden >>= newSLabel) <*> many arg <*> optional tyAnn <?> "Label declaration"
    ref <- scn *> use indent <* svIndent
    indentedItems ref labelDecl (fail "")

  tyRecord = Prod <$> let fieldDecl = (,) <$> (iden >>= newFLabel) <*> tyAnn <?> "Field declaration" in do
    ref <- scn *> use indent <* svIndent
    indentedItems ref fieldDecl (fail "")

  con = let
    fieldAssign = (,) <$> (iden >>= newFLabel) <* reservedOp "=" <*> tt
    multilineAssign = do
      reserved "record"
      ref <- scn *> use indent <* svIndent
      indentedItems ref fieldAssign (fail "")
    conBraces = braces (fieldAssign `sepBy` reservedChar ',')
    in Prod <$> (multilineAssign <|> conBraces)

  branchArrow = reserved "=>" <|> reserved "⇒"
  caseSplits :: Parser [(TT , TT)]
  caseSplits = let split = svIndent *> ((,) <$> tt <* branchArrow <*> tt) :: Parser (TT , TT)
    in braces (split `sepBy` reservedChar ';') <|> let
     finishEarly = (void $ char ')' <|> lookAhead (reservedChar '_'))
     in (use indent <* scn) >>= \ref -> indentedItems ref split finishEarly
  lambdaCase = BruijnLam . BruijnAbsF 1 [] 0 . CasePat . CaseSplits (Var (VBruijn 0)) <$> caseSplits 
  casePat = (\tt splits -> CasePat (CaseSplits tt splits)) <$> tt <* reserved "of" <*> caseSplits

  letIn = let -- svIndent -- tell linefold (and subsequent let-ins) not to eat our indentedItems
    pLetQual = choice ((\(txt , l) -> reserved txt $> l) <$> [("let" , Let) , ("rec" , Rec) , ("mut" , Mut)])
    in pLetQual >>= pBlock >>= \block -> LetIn block <$> (reserved "in" *> (Just <$> tt))

  typedTT = pure

pBlock :: LetRecT -> Parser Block
pBlock letTy = scn *> use indent >>= \ref -> Block True letTy <$> parseDecls ref

---------------------
-- literal parsers --
---------------------
literalP = let
  signed p = let
    sign :: Bool -> Parser Bool =
      \i -> option i $ single '+' *> sign i <|> single '-' *> sign (not i)
    in sign False >>= \s -> p <&> \n -> if s then negate n else n
  -- L.charLiteral handles escaped chars (eg. \n)
  char :: Parser Char = between (single '\'') (single '\'') L.charLiteral
  stringLiteral :: Parser [Char] = choice
    [ single '"'      *> manyTill L.charLiteral (single '"')
    , string "''"     *> manyTill L.charLiteral (string "''")
    , string "$"      *> manyTill L.charLiteral endLine
    ] <?> "String literal"
  intLiteral = choice
    [ try (signed L.decimal)
    , string "0b" *> L.binary
    , string "0o" *> L.octal
    , string "0x" *> L.hexadecimal
    ] <?> "integer literal"
  in choice
   [ Char   <$> char
   , String <$> stringLiteral
   , Int    <$> intLiteral
   , numP
   ] <?> "literal"

numP :: Parser Literal = let decimal_ = takeWhile1P (Just "digit") isDigit :: Parser Text in do
  c <- decimal_
  f <- option T.empty (char '.'  *> decimal_)
  e <- option T.empty (char' 'e' *> decimal_)
  pure $ if T.null f && T.null e then PolyInt c else PolyFrac $ c `T.snoc` '.' `T.append` f `T.append` e
