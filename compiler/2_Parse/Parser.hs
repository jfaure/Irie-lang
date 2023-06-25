module Parser (parseModule , parseMixFixDef) where
import Prim ( Literal(..) )
import ParseSyntax as P
import MixfixSyn ( defaultPrec, Assoc(..), MFWord(..), MixfixDef(..), Prec(Prec) )
import Text.Megaparsec
import Text.Megaparsec.Char ( char, char', string )
import qualified Data.Vector as V
import System.FilePath.Posix as FilePath (dropExtension , takeFileName)
import qualified Text.Megaparsec.Char.Lexer as L ( binary, charLiteral, hexadecimal, octal, skipLineComment, space, symbol, decimal, indentLevel, lexeme )
import Control.Monad (fail)
import Control.Lens
import qualified Data.Map.Strict as M
import qualified Data.Set as S ( fromList, member )
import qualified Data.Text as T ( any, append, concat, null, snoc, empty )
import Data.Functor.Foldable
--import qualified Text.Megaparsec.Debug as DBG
-- dbg i = DBG.dbg i
--showN n = try ((takeP Nothing n >>= traceShowM) *> fail "debug parser") <|> pure () :: Parser ()

-- The initial parse is context-insensitive: forward | mutual definitions and mixfixes are resolved later
-- Parsing converts all text names to INames (Int) and doesn't depend on imports
type Parser = ParsecT Void Text (Prelude.State ParseState)

--------------------------
-- Parsestate functions --
--------------------------
addImport i = moduleWIP . imports %= (i:)
addMFWord :: HName -> (Int -> MFWord) -> Parser IName
addMFWord h mfw = do
  sz <- addName h -- moduleWIP . parseDetails .  hNameMFWords . _1 <<+= 1
  sz <$ (moduleWIP . parseDetails . hNameMFWords %= M.insertWith (++) h [mfw sz])

-- insertLookup is tricky but saves a log(n) operation
insertOrRetrieve :: HName -> HNameMap -> (IName , HNameMap)
insertOrRetrieve h (sz , hList , mp) = case M.insertLookupWithKey (\_k _new old -> old) h sz mp of
  (Just x , mp) -> (x  , (sz     , hList     , mp)) -- retrieve
  (_      , mp) -> (sz , (sz + 1 , h : hList , mp)) -- insert

addName :: HName -> Parser IName
addName h = moduleWIP . parseDetails . hNamesToINames %%= insertOrRetrieve h
-- promote INames to topINames by assigning a new IName from hereon out
-- if an IName is already a topIName then the IName can be reassigned everywhere:
--  topINames bitset resolves its bind index correctly, duplicate topbind names are caught by scope
addNewName h = use (moduleWIP . parseDetails . topINames) >>= \top ->
  moduleWIP . parseDetails . hNamesToINames %%= \(sz , hList , mp) ->
  case M.insertLookupWithKey (\_k new old -> if testBit top old then old else new) h sz mp of
    (x , mp) | Just v <- x , testBit top v -> (v , (sz , hList , mp))
    (_ , mp) -> (sz , (sz + 1 , h : hList , mp))

addTopName h = addNewName h >>= \i -> i <$ (moduleWIP . parseDetails . topINames%= \top -> setBit top i)
newFLabel h  = addName h >>= \i -> i <$ (moduleWIP . parseDetails . fieldINames %= \top -> setBit top i)
newSLabel h  = addName h >>= \i -> i <$ (moduleWIP . parseDetails . labelINames %= \top -> setBit top i)

-----------
-- Lexer --
-----------
-- A key convention: consume trailing whitespace (use `symbol` or `lexeme`)
--  => Parsers can assume they start on a non-blank.
-- Space consumers: scn eats newlines, sc does not.
-- Save newline offsets so we can recover line-numbers from the stream offset : Nat
addNewlineOffset :: Parser ()
addNewlineOffset = getOffset >>= \o -> moduleWIP . parseDetails . newLines %= (o - 1 :)
endLine = lexeme (single '\n') *> addNewlineOffset

isHSpace x = isSpace x && x /= '\n' && x /= '\t' -- isHSpace , but handles all unicode spaces
tabsc :: Parser () = L.space (void $ takeWhile1P (Just "tabs") (== '\t')) lineComment blockComment
-- TODO sc shouldn't eat tabs | check if file convention uses tab/space indent
sc  :: Parser () = L.space (void $ takeWhile1P (Just "white space") isHSpace) lineComment blockComment
scn :: Parser () = let
  space1 = sc *> some endLine *> skipMany (sc *> endLine)
  in L.space space1 lineComment blockComment
scnTabs :: Parser () = let
  space1 = sc *> some endLine *> skipMany (tabsc *> endLine)
  in L.space space1 lineComment blockComment

lineComment = L.skipLineComment "--"
blockComment = let
  skipBlockComment start end = void $ string start
    *> manyTill (endLine <|> blockComment <|> void anySingle) end
  in skipBlockComment "{-" "-}" <|> skipBlockComment "(*" "*)"

lexeme, lexemen :: Parser a -> Parser a -- parser then whitespace
lexeme  = L.lexeme sc
lexemen = L.lexeme scn
symbol :: Text -> Parser Text --verbatim strings
symbol = L.symbol sc

betweenS = between `on` symbol
parens, braces, brackets :: Parser a -> Parser a
parens    = betweenS "(" ")"
braces    = betweenS "{" "}"
brackets  = betweenS "[" "]"

-- prev = reference indent level
-- lvl  = lvl of first indented item
indentedItems :: Pos -> Parser a -> Parser () -> Parser [a]
indentedItems prev p stop = let
  go lvl = try $ indentn *> do
    [] <$ lookAhead (eof <|> stop) <|> (checkIndent prev lvl *> p >>= \ok -> option [ok] ((ok :) <$> go lvl))
  in L.indentLevel >>= go

-- indentedItems using the state-saved (svIndent) reference
-- This is the more useful function for parsing indented Items
pIndentedItems p finish = scn *> use indent <* svIndent
  >>= \ref -> indentedItems ref p finish

checkIndent :: Pos -> Pos -> Parser ()
checkIndent prev lvl = L.indentLevel >>= \pos -> {-d_ (pos , prev , lvl) $-} if
 | pos == lvl  -> pure ()
 | pos <= prev -> fail ("expected indented items, got: " <> show pos <> " <= " <> show prev)
 | otherwise   -> fail ("incorrect indentation, got: " <> show pos <> ", expected " <> show lvl <> " (<= " <> show prev <>")")

indentn = use indentType >>= \case
  IndentTab    -> scnTabs
  IndentSpace  -> scn
  IndentEither -> scnTabs <* (indentType .= IndentTab) <|> scn <* (indentType .= IndentSpace)

-- tells linefold and let-ins not to eat our indentedItems
svIndent = L.indentLevel >>= (indent <.=)

-- Linefolds must start at higher than reference indent, but then can parse multiple lines at this indent
linefolds :: Parser a -> Parser [a]
linefolds p = endLine *> scn *> do
  prev <- use indent
  cur  <- svIndent
  when (cur <= prev) (fail $ "not a linefold " <> show prev <> ", expected >= " <> show cur)
  args <- indentedItems cur (some p) (fail "")
  (concat args ++) <$> (try (linefolds p) <|> pure [])

-----------
-- Names --
-----------
reservedChars = "@(){};:,\"\\λ" -- \\ λ necessary?
reservedNamesL = words "? _ let rec mut \\case λcase case # record data gadt as over of _ import use open = ? | => ⇒ in <-"
--reservedIMap = M.fromList (zip reservedNamesL [0..])

reservedNames = S.fromList reservedNamesL
-- check the name isn't an iden which starts with a reservedWord
reservedName w = (void . lexeme . try) (string w *> notFollowedBy idenChars)
reservedChar c = if T.any (==c) reservedChars then lexeme (char c) else lexeme (char c <* notFollowedBy idenChars)
reserved = reservedName
isIdenChar x = not (isSpace x || T.any (==x) reservedChars)
idenChars = takeWhile1P Nothing isIdenChar
checkReserved x = x <$ when (x `S.member` reservedNames) (fail ("keyword '" <> toS x <> "' cannot be an identifier"))
--checkLiteral x  = x <$ when (isDigit `T.all` x) -- TODO not good enough (1e3 , 2.0 etc..)
--  (fail ("literal: '" <> toS x <> "' cannot be an identifier"))
checkIden = checkReserved -- <=< checkLiteral
--anyIden = lexeme (idenChars <* notFollowedBy idenChars) -- incl. reserved

-- We must use 'try', to backtrack if we ended up parsing a reserved word
iden :: Parser HName = lexeme . try $ (idenChars >>= checkIden)
idenNo_ = lexeme idenNo_'
idenNo_' = let
  -- Allow '.' in names but only if name starts with '.' and isn't "."
--dotIden = lookAhead (char '.' *> (char '.' <|> satisfy isIdenChar))
--  *> takeWhile1P Nothing (\x -> isIdenChar x || x == '.')
  in try ((takeWhile1P Nothing (\x -> isIdenChar x && x /= '_') {-<|> dotIden-}) >>= checkIden)

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
  parseModule = scn *> (parseBinds True >>= (moduleWIP . bindings .=)) *> eof *> use moduleWIP
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
 [ reserved "import"  <* (iden <&> PImport >>= addImport)
 , reserved "imports" <* some (iden <&> PImport >>= addImport)
 , reserved "open"    <* (iden <&> POpen >>= addImport)
 , reserved "opens"   <* some (iden <&> POpen >>= addImport)
-- , reserved "use"     <* (iden >>= addImport)
 ]

parseBinds :: Bool -> Parser (V.Vector FnDef)
parseBinds isTop = let
  sep = eof <|> (endLine *> scn) --  *> when (prev < lvl) (fail "unexpected top level indentation"))
  in scn *> parseDecls isTop sep

newtype SubParser = SubParser { unSubParser :: Parser (Maybe (FnDef , SubParser)) }
parseDecls :: Bool -> Parser () -> Parser (V.Vector FnDef)
parseDecls isTop sep = V.unfoldrM unSubParser (pDecl isTop sep)

pDecl :: Bool -> Parser () -> SubParser
pDecl isTop sep = SubParser $ many (lexemen pImport) *> svIndent *> let
  subParse = SubParser (option Nothing $ sep *> unSubParser (pDecl isTop sep))
  -- parse a name and consume all idenChars; ie. if expecting "take", don't parse "takeWhile"
  pName nm = lexeme (string nm *> lookAhead (satisfy (not . isIdenChar)))
  pRhs = lexemen (reserved "=") *> tt
  fnMatch :: Parser [TT] -> Parser TT
  fnMatch pMFArgs = GuardArgs <$> pMFArgs <*> (patGuards pRhs <|> pRhs)
  pEqns :: Parser [TT] -> Parser [TT] -> Parser [TT]
  pEqns pArgs pMFArgs = let -- first parse is possibly different
    in (:) <$> fnMatch pArgs
           <*> many (try $ endLine *> scn *> svIndent *> fnMatch pMFArgs)
      <|> some (try (endLine *> fnMatch pMFArgs))
  mkFnEqns = \case { [x] -> x ; xs -> FnEqns xs }
  in option Nothing $ getOffset >>= \srcOff -> optional (reserved "rec") *> lexeme pMixfixWords >>= \case
    [Just nm] -> let pArgs = many (lexeme singlePattern) in do
      iNm <- if isTop then addTopName nm else addName nm
      moduleWIP . parseDetails . thisBind .= iNm
      sig <- optional (tyAnn <* try (endLine *> scn *> pName nm))
      rhsTT <- mkFnEqns <$> pEqns pArgs (pName nm *> pArgs)
      let rhs = maybe rhsTT (Typed rhsTT) sig
      pure $ Just (FnDef nm iNm Let Nothing rhs srcOff , subParse)
    mfDefHNames   -> let
      pMixFixArgs = cata $ \case
        Nil      -> pure []
        Cons m x -> maybe ((:) <$> lexeme singlePattern <*> x) (\nm -> pName nm *> x) m
      nm = mixFix2Nm mfDefHNames
      in mdo -- for mfdef
      let mfDef = MixfixDef iNm mfDefINames prec
      iNm  <- if isTop then addTopName nm else addName nm -- <* when isTop (void $ addTopName nm)
      moduleWIP . parseDetails . thisBind .= iNm
      prec <- fromMaybe defaultPrec <$> optional (braces parsePrec)
      mfDefINames <- addMixfixWords mfDefHNames mfDef
      sig <- optional (tyAnn <* try (endLine *> scn *> pName nm))
      rhsTT <- mkFnEqns <$> pEqns (pure []) (pMixFixArgs mfDefHNames)
      let rhs = maybe rhsTT (Typed rhsTT) sig
      pure $ Just (FnDef nm iNm Let (Just mfDef) rhs srcOff , subParse)

lambda = glambda (reserved "=>" <|> reserved "⇒" <|> reserved "=")
glambda sep = (\ars rhs -> if null ars then rhs else GuardArgs ars rhs) <$> many singlePattern <* lexemen sep <*> tt
tyAnn = reservedChar ':' *> tt

-- make a lambda around any '_' found within the tt eg. `(_ + 1)` => `\x => x + 1`
catchUnderscoreAbs = pure

singlePattern = ttArg -- pattern TTs are inversed later
tt :: Parser TT
(tt , ttArg) = (anyTT , arg) where
  anyTT = ({-tySum <|>-} appOrArg) >>= catchUnderscoreAbs >>= typedTT <?> "tt"
   -- lens '.' binds tighter than App
  argOrLens = arg >>= \larg -> option larg (try $ lens larg)
  lineFoldArgs p = many p >>= \ars -> (ars ++) <$> (try (linefolds p) <|> pure [])
  appOrArg' o  = argOrLens >>= \larg -> option larg $ case larg of
    P.Label l [] -> P.Label l <$> lineFoldArgs argOrLens
    fn     -> (\args -> if null args then fn else Juxt o (fn : args)) <$> lineFoldArgs argOrLens
  appOrArg = getOffset >>= \o -> appOrArg' o
    <|> (lineFoldArgs argOrLens >>= \args -> if null args then fail "Expected linefold" else pure (Juxt o args))
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
   , letIn =<< choice ((\(txt , l) -> reserved txt $> l) <$> [("let" , Let) , ("rec" , Rec) , ("mut" , Mut)])
   , (reserved "\\case" <|> reserved "λcase") *> lambdaCase <?> "Lambda case"
   , (reservedChar '\\' <|> reservedChar 'λ') *> lambda <?> "Lambda"
-- , reserved "do" *> doExpr
   , reserved "record" *> conMultiline <&> Prod . V.fromList <?> "Record"
   , reserved "case"   *> casePat   <?> "Case_of__"
   , reserved "data"   *> pData <?> "Data declaration"
   , reserved "gadt"   *> pGadt    <?> "Gadt declaration"
   , reserved "##" *> (PLitArray <$> lineFoldArgs literalP) <?> "Literal array"
   , reserved "#" *> (PArray <$> lineFoldArgs ttArg) <?> "Literal array"
   , reservedChar '@' *> idenNo_ >>= newSLabel <&> \l -> P.Label l []
   , braces conBraces <&> Prod . V.fromList <?> "record"
   , parens ((tt >>= \t -> option t (tuple t <|> typedTT t)) <|> scn $> Tuple []) >>= catchUnderscoreAbs
   , literalP <&> Lit -- ! before iden parser
   , iden >>= addName <&> VParseIName
     -- (? support partial mixfix aps eg. if_then a else b)
   ] <?> "TT Argument"
  letIn letQual = do
    block <- Block True letQual <$> parseBinds False 
    liftLetStart <- moduleWIP . parseDetails . letBindCount <<+= V.length (binds block)
    LetIn block liftLetStart <$> (scn *> reserved "in" *> tt)

  pData = do
    let labelDecl = (,) <$> (iden >>= newSLabel) <*> many arg
    alts <- pIndentedItems labelDecl (fail "")
    let altINames = alts <&> \(l , _) -> l
--  liftLetStart <- moduleWIP . parseDetails . letBindCount <<+= length alts
    use (moduleWIP . parseDetails . thisBind) >>= \this -> addImport (POpenData this{-liftLetStart-} altINames)
    pure (Data alts)

-- , brackets tt <&> TyListOf
  pGadt = Gadt <$> let -- vec : (n : Nat) ~> Vector n x = gadt
    gadtDecl = (,) <$> (iden >>= newSLabel) <*> tyAnn
    in pIndentedItems gadtDecl (fail "")

  tuple t = (\ts -> Tuple (t:ts)) <$> some (reservedChar ',' *> tt)
  conFieldDecl = (,) <$> (iden >>= newFLabel) <* reservedChar '=' <*> tt <?> "Field assignment"
  conMultiline = pIndentedItems conFieldDecl (fail "")
  conBraces    = conFieldDecl `sepBy` reservedChar ','

  caseSplits :: Parser [(TT , TT)]
  caseSplits = let
    branchArrow = reserved "=>" <|> reserved "⇒"
    rhs = branchArrow *> tt
    split  = svIndent *> ((,) <$> tt <*> (rhs <|> patGuards rhs))
    in braces (split `sepBy` reservedChar ';') <|> let
     finishEarly = void (char ')' <|> char '}' <|> char ']')
     in option [] (pIndentedItems split finishEarly)
  lambdaCase = LambdaCase . CaseSplits' <$> caseSplits
  casePat = (\tt splits -> CasePat (CaseSplits tt splits)) <$> tt <* reserved "of" <*> caseSplits

  typedTT t = option t (Typed t <$> tyAnn)

patGuards :: Parser TT -> Parser TT
patGuards rhs = let
  patGuard = tt >>= \pGuard -> option (GuardBool pGuard) (GuardPat pGuard <$> (reservedName "<-" *> tt))
  in reservedChar '|' *> (Guards Nothing <$> (patGuard `sepBy1` char ',') <*> rhs)

---------------------
-- literal parsers --
---------------------
literalP = lexeme $ try $ (<* notFollowedBy iden) $ let
  signed p = let
    sign :: Bool -> Parser Bool =
      \i -> option i $ single '+' *> sign i <|> single '-' *> sign (not i)
    in sign False >>= \s -> p <&> \n -> if s then negate n else n
  -- L.charLiteral handles escaped chars (eg. \n)
  stringLiteral :: Parser [Char] = choice
    [ single '"'  *> manyTill L.charLiteral (single '"')
    , string "''" *> manyTill L.charLiteral (string "''")
    , string "$"  *> manyTill L.charLiteral endLine
    ] <?> "String literal"
  intLiteral = char '0' *> choice
    [ (char 'b' <|> char 'B') *> L.binary
    , (char 'o' <|> char 'O') *> L.octal
    , (char 'x' <|> char 'X') *> L.hexadecimal
    , L.decimal
    , pure 0
    ] <?> "integer literal"
  mkInt i
    | i == 0 || i == 1 = Fin 1 i
    | i < 256 = Fin 8 i
    | True    = Fin 32 (fromIntegral i)
  in choice
   [ Char   <$> between (single '\'') (single '\'') L.charLiteral
   , String <$> stringLiteral
   , mkInt  <$> signed (intLiteral <|> L.decimal)
   , numP
   ] <?> "literal"

numP :: Parser Literal = let decimal_ = takeWhile1P (Just "digit") isDigit :: Parser Text in do
  c <- decimal_
  f <- option T.empty (char '.'  *> decimal_)
  e <- option T.empty (char' 'e' *> decimal_)
  pure $ if T.null f && T.null e then PolyInt c else PolyFrac $ c `T.snoc` '.' `T.append` f `T.append` e
