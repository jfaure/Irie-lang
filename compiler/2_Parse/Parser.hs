{-# Language NoTypeFamilies #-}
module Parser (parseModule , parseMixFixDef) where
-- The initial parse is context-insensitive: forward / mutual definitions and mixfixes are resolved later
-- Parsing converts all text names to INames (Int) and doesn't depend on imports

import Prim ( Literal(PolyFrac, Char, String, Int, PolyInt) )
import ParseSyntax as P
import MixfixSyn ( defaultPrec, Assoc(..), MFWord(..), MixfixDef(..), Prec(Prec) )
import UnPattern (matchesToTT)
import Text.Megaparsec
import Text.Megaparsec.Char ( char, char', string )
import System.FilePath.Posix as FilePath (dropExtension , takeFileName)
import qualified Text.Megaparsec.Char.Lexer as L ( binary, charLiteral, hexadecimal, octal, skipLineComment, space, symbol, decimal, indentLevel, lexeme )
import Control.Monad (fail)
import Control.Lens
import qualified Data.Map.Strict as M
import qualified Data.Set as S ( fromList, member )
import qualified Data.Text as T ( all, any, append, concat, null, snoc, empty )
import MUnrolls
--import qualified Text.Megaparsec.Debug as DBG

-- debug fns
--dbg i = DBG.dbg i
--showN n = try ((takeP Nothing n >>= traceShowM) *> fail "debug parser") <|> pure () ∷ Parser ()

type Parser = ParsecT Void Text (Prelude.State ParseState)

--------------------------
-- Parsestate functions --
--------------------------
addBind b     = moduleWIP . bindings   %= (b:)
addImport i   = moduleWIP . imports    %= (i:)

addMFWord h mfw = do
  sz <- moduleWIP . parseDetails . hNameMFWords . _1 <<%= (+1)
  moduleWIP . parseDetails . hNameMFWords . _2 %= M.insertWith (++) h [mfw sz]
  pure sz

-- The trickiness below is due to insertLookup, which saves a log(n) operation
-- Data.Map's builtin size is good enough for labels/fields
insertOrRetrieve :: HName -> Map HName Int -> (Either Int Int, Map HName Int)
insertOrRetrieve h mp = let sz = M.size mp in case M.insertLookupWithKey (\_k _new old -> old) h sz mp of
  (Just x, mp) -> (Right x  , mp)
  (_,mp)       -> (Left  sz , mp)

addBindName :: HName -> Parser IName
addBindName h = eitherOne <$> (moduleWIP . parseDetails . hNameBinds %%= insertOrRetrieve h)

eitherOne = \case { Right r -> r ; Left r -> r }
addUnknownName h = eitherOne <$> (moduleWIP . parseDetails . hNamesNoScope %%= insertOrRetrieve h)

newFLabel h    = eitherOne <$> (moduleWIP . parseDetails . fields %%= insertOrRetrieve h)
newSLabel h    = eitherOne <$> (moduleWIP . parseDetails . labels %%= insertOrRetrieve h)
lookupSLabel h = (M.!? h)  <$> use (moduleWIP . parseDetails . labels)

lookupBindName h = Var . VExtern <$> addUnknownName h -- use (moduleWIP . parseDetails) >>= \p -> let

-----------
-- Lexer --
-----------
-- A key convention: tokens consume trailing whitespace (using `symbol` or `lexeme`)
-- so parsers can assume they start on a non-blank.
-- Space consumers: scn eats newlines, sc does not.
-- Save newline offsets so we can track source locations using a single Int
addNewlineOffset ∷ Parser ()
addNewlineOffset = getOffset >>= \o -> moduleWIP . parseDetails . newLines %= (o - 1 :)
isHSpace x = isSpace x && x /= '\n' && x /= '\t' -- isHSpace , but handles all unicode spaces
tabsc ∷ Parser () = L.space (void $ takeWhile1P (Just "tabs") (== '\t')) lineComment blockComment
-- TODO sc shouldn't eat tabs?
sc  ∷ Parser () = L.space (void $ takeWhile1P (Just "white space") isHSpace) lineComment blockComment
scn ∷ Parser () = let
  space1 = sc *> some endLine *> skipMany (sc *> endLine)
  in L.space space1 lineComment blockComment
scnTabs ∷ Parser () = let
  space1 = sc *> some endLine *> skipMany (tabsc *> endLine)
  in L.space space1 lineComment blockComment

endLine = lexeme (single '\n') <* addNewlineOffset
lineComment = L.skipLineComment "--" -- <* addNewlineOffset
blockComment = let -- still need to count newlines
  skipBlockComment start end = string start
    *> manyTill (endLine {-<|> blockComment nested-} <|> anySingle) end
  in void $ skipBlockComment "{-" "-}" <|> skipBlockComment "(*" "*)"

lexeme, lexemen ∷ Parser a -> Parser a -- parser then whitespace
lexeme  = L.lexeme sc
lexemen = L.lexeme scn
symbol ∷ Text -> Parser Text --verbatim strings
symbol = L.symbol sc

parens, braces, brackets ∷ Parser a -> Parser a
parens    = symbol  "(" `between` symbol  ")"
braces    = symbol  "{" `between` symbol  "}"
brackets  = symbol  "[" `between` symbol  "]"

-- ref = reference indent level
-- lvl = lvl of first indented item (often == pos)
indentedItems prev p finished = let
 go lvl = indentn *> do
  pos <- L.indentLevel
--svIndent
  [] <$ lookAhead (eof <|> finished) <|> if
 -- 'fail' here to backtrack the whitespace/newlines. Otherwise the App parser sees and eats things from later lines
    | pos <= prev -> fail ("end of indent: " <> show pos <> " <= " <> show prev)
    | pos == lvl  -> p >>= \ok -> option [ok] ((ok :) <$> try (go lvl))
    | otherwise   -> fail ("incorrect indentation, got " <> show pos <> ", expected " <> show lvl <> " (<= " <> show prev <>")")
     -- L.incorrectIndent EQ lvl pos
 in L.indentLevel >>= go

indentn = use indentType >>= \case
  IndentTab    -> scnTabs
  IndentSpace  -> scn
  IndentEither -> scnTabs <* (indentType .= IndentTab) <|> scn <* (indentType .= IndentSpace)

-- tells linefold and let-ins not to eat our indentedItems
svIndent = L.indentLevel >>= (indent .=)

linefold p = endLine *> scn *> do
  prev <- use indent
  cur  <- L.indentLevel
  svIndent
  when (cur <= prev) (fail $ "not a linefold " <> show prev <> ", expected >= " <> show cur)
  p

-----------
-- Names --
-----------
reservedChars = ".@(){};:,\\\""
reservedNames = S.fromList $ words "let rec in \\case λcase case as over foreign foreignVarArg where of _ import use open require = ? | λ => ⇒"
-- check the name isn't an iden which starts with a reservedWord
reservedName w = (void . lexeme . try) (string w *> notFollowedBy idenChars)
reservedChar c
  | T.any (==c) reservedChars = lexeme (char c)
  | otherwise = lexeme ((char c) <* notFollowedBy idenChars)
reservedOp = reservedName
reserved = reservedName
isIdenChar x = not (isSpace x || T.any (==x) reservedChars)
idenChars = takeWhile1P Nothing isIdenChar
checkReserved x = x <$ when (x `S.member` reservedNames) (fail ("keyword '" <> toS x <> "' cannot be an identifier"))
checkLiteral x  = x <$ when (isDigit `T.all` x) -- TODO not good enough (1e3 , 2.0 etc..)
  (fail ("literal: '" <> toS x <> "' cannot be an identifier"))
checkIden = checkReserved <=< checkLiteral

-- We must use 'try', to backtrack if we ended up parsing a reserved word
iden ∷ Parser HName = lexeme . try $ (idenChars >>= checkIden)
idenNo_ = lexeme idenNo_'
idenNo_' = try (takeWhile1P Nothing (\x->isIdenChar x && x /= '_') >>= checkIden)

-- separated and split on '_' (ie. argument holes)
pMixfixWords ∷ Parser [Maybe Text] = lexeme $ do
  some (choice [Nothing <$ char '_' , Just <$> idenNo_']) >>= \case
    [Nothing] -> fail "'_' cannot be an identifier"
    mf -> pure mf
-- exported convenience function for use by builtins (Externs.hs)
parseMixFixDef ∷ Text -> Either (ParseErrorBundle Text Void) [Maybe Text]
 = \t -> runParserT pMixfixWords "<internal>" t `evalState` _

------------
-- Parser --
------------
parseModule ∷ FilePath -> Text -> Either (ParseErrorBundle Text Void) Module
  = \nm txt -> let
  end = (bindings %~ reverse)
  in end <$> runParserT (scn *> doParse *> eof *> use moduleWIP) nm txt
  `evalState` ParseState {
       _indent      = mkPos 1
     , _indentType  = IndentEither
     , _moduleWIP   = emptyParsedModule (toS (dropExtension (takeFileName nm)))
     }

-- group declarations as they are parsed
doParse = void $ decl `sepEndBy` (optional endLine *> scn) ∷ Parser ()
decl = svIndent *> choice
   [ reserved "import" *> (iden >>= addImport)
   , reserved "use"    *> (iden >>= addImport) -- TODO Scope the names !
-- , void functorModule
-- , pForeign
   , void (funBind True LetOrRec) <?> "binding"
-- , bareTT <?> "repl expression"
   ] <?> "import , extern or local binding"

--bareTT = addAnonBindName *> ((\tt -> addBind (FnDef "replExpr" LetOrRec Nothing 0 [FnMatch [] tt] Nothing)) =≪ tt)

{-
pForeign = do -- external function defined outside of Irie and opaque until link-time
  _fn  <- ((Foreign <$ reserved "foreign") <|> (ForeignVA <$ reserved "foreignVA")) -- TODO use va/not va info
  hNm <- iden
  void (addBindName hNm)
  ty <- reservedOp ":" *> tt
  addBind (FnDef hNm Let Nothing 0 (FnMatch [] (Foreign hNm ty) :| []) (Just ty))
-}

{-
functorModule ∷ Parser ()
functorModule = reserved "module" *> do
  mName     <- idenNo_
  use (moduleWIP . moduleName) >>= \case
    Right prevMName -> fail $ toS $ "Too many 'module' declarations in '" <> prevMName <> "'"
    Left fName -> if mName /= fName
      then fail $ toS $ "Module name '" <> mName <> "' does not match file name '" <> fName <> "'"
--    else (moduleWIP . parseDetails . hNameArgs %= (M.empty :)) *> do -- TODO this is a weird first Half of a new-argnest
      else void $ newArgNest $ do
        moduleWIP . moduleName .= Right mName
        o <- getOffset
        args    <- some pattern
        sig     <- optional (reserved ":" *> tt)
        unless (null args && isNothing sig) (moduleWIP . functor .= Just (FunctorModule args sig o))
        reserved "="
-}

-------------------
-- Function defs --
-------------------
mixFix2Nm = T.concat . map (\case { Just nm->nm ; Nothing->"_" })
parsePrec = let
  assoc = choice [Assoc <$ single 'a' , AssocRight <$ single 'r' , AssocLeft <$ single 'l' , AssocNone <$ single 'n']
  in lexeme $ Prec
  <$> (assoc     <?> "assoc : [a | l | r | n]")
  <*> (L.decimal <?> "precedence (an integer)")

addMixfixWords m mfdef = let
  addMFParts mfp = mfp `forM` \case
    Just hNm -> Just <$> addMFWord hNm MFPart
    Nothing  -> pure Nothing
  in case m of
    Just hNm           : mfp -> addMFWord hNm (StartPrefix mfdef)
      >>= \w -> (Just w : )              <$> addMFParts mfp
    Nothing : Just hNm : mfp -> addMFWord hNm (StartPostfix mfdef)
      >>= \w -> (Nothing :) . (Just w :) <$> addMFParts mfp
    _ -> fail "panic: internal parse error with mixfixes"

some1 f = (:|) <$> f <*> many f

funBind ∷ Bool -> LetRecT -> Parser (IName , TT)
funBind mkBind letRecT = (<?> "binding") $ optional (reserved "rec") *> lexeme pMixfixWords >>= \case
  [Just nm] -> let pArgs = many (lexeme singlePattern) -- non-mixfix fn def can parse args immediately
    in funBind' mkBind pArgs letRecT nm Nothing (symbol nm *> pArgs)
  mfdefHNames -> let
--  hNm = mixFix2Nm mfdefHNames
    pMixFixArgs = \case
      []           -> pure []
      Just  nm : x -> symbol nm *> pMixFixArgs x
      Nothing  : x -> (:) <$> lexeme singlePattern <*> pMixFixArgs x
    in mdo
    prec <- fromMaybe defaultPrec <$> optional (braces parsePrec)
    mfdefINames <- addMixfixWords mfdefHNames mfdef
    let mfdef = MixfixDef iNm mfdefINames prec
    (iNm , tt) <- funBind' mkBind (pure []) letRecT (mixFix2Nm mfdefHNames) (Just mfdef) (pMixFixArgs mfdefHNames)
    pure (iNm , tt)

-- parse a function definition (given a possible mixfix pattern parsed in the type annotation)
-- => pMFArgs parses extra equations on subsequent lines
-- If this is a mixfix, args will be [] at this point
funBind' ∷ Bool -> Parser [Pattern] -> LetRecT -> Text -> Maybe MixfixDef -> Parser [Pattern] -> Parser (IName , TT)
funBind' mkBind pArgs letRecT nm mfDef pMFArgs = (<?> "function body") $ mdo
  let body = matchesToTT eqns -- NonEmpty FnMatch -> BruijnAbsF TT
  iNm <- if mkBind
    then addBindName nm <* addBind (FnDef nm letRecT mfDef body ann) -- add in mfix in case of recursive references
    else addUnknownName nm -- let-bound
  (eqns , ann) <- do
    ann  <- optional tyAnn
    eqns <- choice -- TODO maybe don't allow `_+_ a b = add a b`
--    [ (:|) <$> (fnMatch pArgs (reserved "=")) <*> many (try (endLine *> fnMatch pMFArgs (reserved "=")))
      [ (:|) <$> (fnMatch pArgs (reserved "="))
             <*> many (try $ endLine *> scn *> svIndent *> fnMatch pMFArgs (reserved "="))
      , case ann of
          Nothing -> some1 $ try (endLine *> fnMatch pMFArgs (reserved "=")) -- f = _
          Just{}  -> some1 $ try (endLine *> fnMatch pMFArgs (reserved "=")) -- f : T = _
      ]
    pure (eqns , ann)
  pure (iNm , body)

tyAnn ∷ Parser TT = reservedChar ':' *> tt -- do {-newArgNest $-} -- no freeVars in a pi-binder

lambda = do
  (eqns {-, free-}) <- {-newArgNest $-} (:|[]) <$> fnMatch (many singlePattern) (reserved "=>" <|> reserved "⇒" <|> reserved "=")
  pure $ matchesToTT eqns

fnMatch pMFArgs sep = FnMatch <$> (pMFArgs <* lexemen sep) <*> tt

-- make a lambda around any '_' found within the tt eg. `(_ + 1)` ⇒ `\x ⇒ x + 1`
catchUnderscoreAbs = pure

tt ∷ Parser TT
(tt , ttArg) = (anyTT , arg)
  where
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
  lens ∷ TT -> Parser TT
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
  implicitPiBound t = option t $ reserved ":" *> tt <&> PiBound [t]
--parensExpr = parens (choice [{-try piBound ,-} (tt >>= \t -> tuple t <|> typedTT t) , scn $> Prod []] >>= implicitPiBound) >>= catchUnderscoreAbs
  parensExpr = parens (((tt >>= \t -> tuple t <|> typedTT t) <|> scn $> Prod []) >>= implicitPiBound)
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

--doExpr = DoStmts <$> let
--  doStmt = idenNo_ >>= \hNm -> choice
--    [ (reservedName "<-" <|> reserved "<-") *> addArgName hNm >>= \i -> tt <&> Bind i
--    , lookupBindName hNm >>= \i -> tt <&> Sequence . \case
--        App f ars -> App i (f : ars)
--        expr      -> App i [expr]
--    ]
--  in do
--  ref <- use indent <* scn
--  L.indentLevel >>= \i -> case compare i ref of
--    LT -> fail $ "new do statement is less indented than the reference indent: "
--                 <> show i <> " < " <> show ref
--    _  -> indentedItems ref doStmt (void (char ')'))

  branchArrow = reserved "=>" <|> reserved "⇒"
  split = svIndent *> ((,) <$> tt <* branchArrow <*> tt) 
  caseSplits :: Parser [(TT , TT)]
  caseSplits = braces (split `sepBy` reservedChar ';') <|> let
     finishEarly = (void $ char ')' <|> lookAhead (reservedChar '_'))
     in (use indent <* scn) >>= \ref -> indentedItems ref split finishEarly
--lambdaCase = (\(tt , bruijnSubs) -> BruijnLam $ BruijnAbsF 1 bruijnSubs 0 tt)
--  . patternsToCase (Var (VBruijn 0)) <$> caseSplits 
  lambdaCase = BruijnLam . BruijnAbsF 1 [] 0 . CasePat . CaseSplits (Var (VBruijn 0)) <$> caseSplits 
--casePat = (\(t , bruijnSubs) -> trace ("parser ignored bruijnSubs" <> show bruijnSubs) t) . patternsToCase <$> tt <* reserved "of" <*> caseSplits
--casePat = fmap fst $ patternsToCase <$> tt <* reserved "of" <*> caseSplits
  casePat = (\tt splits -> CasePat (CaseSplits tt splits)) <$> tt <* reserved "of" <*> caseSplits

  letIn = let
    pletBinds (letRecT ∷ LetRecT) = do
      scn -- go to first indented binding
      ref <- use indent
      svIndent -- tell linefold (and subsequent let-ins) not to eat our indentedItems
      letBinds <- indentedItems ref (funBind True Let) (reserved "in") <* reserved "in"
      LetBinds letBinds <$> tt
--    let (nmL , rhsL) = unzip letBinds
--    inE <- tt
--    pure $ App (BruijnLam (BruijnAbsF (length nmL) (zip nmL [0..]) 0 inE)) rhsL
    in
      reserved       "let" *> pletBinds Let
        <|> reserved "rec" *> pletBinds Rec

  typedTT = pure

singlePattern = ttArg

---------------------
-- literal parsers --
---------------------
literalP = let
  signed p = let
    sign ∷ Bool -> Parser Bool =
      \i -> option i $ (single '+' *> sign i) <|> (single '-' *> sign (not i))
    in sign False >>= \s -> p <&> \n -> if s then negate n else n
  -- L.charLiteral handles escaped chars (eg. \n)
  char ∷ Parser Char = between (single '\'') (single '\'') L.charLiteral
  stringLiteral ∷ Parser [Char] = choice
    [ single '"'      *> manyTill L.charLiteral (single '"')
    , string "\"\"\"" *> manyTill L.charLiteral (string "\"\"\"") -- triple quotes """
    , string "''"     *> manyTill L.charLiteral (string "''")
    , string "$"      *> manyTill L.charLiteral endLine]
  intLiteral = choice
    [ try (signed L.decimal)
    , string "0b" *> L.binary
    , string "0o" *> L.octal
    , string "0x" *> L.hexadecimal
    ]
  in choice
   [ Char   <$> char
   , String <$> stringLiteral
   , Int    <$> intLiteral
   , numP
   ] <?> "literal"

decimal_ , dotDecimal_ , exponent_ ∷ Parser Text
decimal_    = takeWhile1P (Just "digit") isDigit
dotDecimal_ = char '.' *> decimal_
exponent_   = char' 'e' *> decimal_

numP ∷ Parser Literal = do
  c <- decimal_
  f <- option T.empty dotDecimal_
  e <- option T.empty exponent_
  pure $ if T.null f && T.null e
    then PolyInt c
    else PolyFrac $ c `T.snoc` '.' `T.append` f `T.append` e
