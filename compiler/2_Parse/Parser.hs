module Parser (parseModule , parseMixFixDef) where
-- Parsing is responsible for converting all text names to int indexes into various vectors
--   1. VBind:   top-level let bindings
--   2. VLocal:  lambda-bound arguments
--   3. VExtern: out-ofscope HNames inamed now and resolved later
-- * name scope is checked and free variables are noted
-- * we cannot resolve externs (incl forward refs) or mixfixes yet.
--
-- Note: add corresponding bind immediately after adding an IName (can resort to recursiveDo)

import Prim
import ParseSyntax as P
import MixfixSyn
import Text.Megaparsec-- hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.IntSet as IS
import qualified Data.Set as S
import Control.Monad (fail)
import Control.Lens
--import qualified Text.Megaparsec.Debug as DBG
dbg i = identity -- DBG.dbg i

type Parser = ParsecT Void Text (Prelude.State ParseState)

--------------------------
-- Parsestate functions --
--------------------------
addBind b     = moduleWIP . bindings   %= (b:)
addImport i   = moduleWIP . imports    %= (i:)
addExtern e   = moduleWIP . externFns  %= (e:)
addPiBound  p = piBound %= \(x:xs)->(p:x):xs
getPiBounds f = do
  piBound %= ([]:)
  r <- f
  pis <- fromMaybe (panic "impossible: empty pibound stack") . head <$> (piBound <<%= drop 1)
  pure (pis , r)

addMFWord h mfw = do
  sz <- moduleWIP . parseDetails . hNameMFWords . _1 <<%= (+1)
  moduleWIP . parseDetails . hNameMFWords . _2 %= M.insertWith (++) h [mfw sz]
  pure sz

il = M.insertLookupWithKey (\k new old -> old)
-- Data.Map's builtin size is good enough for labels/fields
insertOrRetrieve h mp = let sz = M.size mp in case il h sz mp of
  (Just x, mp) -> (Right x  , mp)
  (_,mp)       -> (Left  sz , mp)
-- custom size variable (anonymous binds aren't named in the map)
insertOrRetrieveSZ h (sz,mp) = case il h sz mp of
  (Just x, mp) -> (Right x , (sz,mp))
  (_,mp)       -> (Left sz , (sz+1,mp))
-- the list of args corresponds to a nest of function defs
-- if we're adding an argument, we do so to the first (innermost level)
insertOrRetrieveArg :: Text -> Int -> [M.Map Text Int] -> (Either Int Int, [M.Map Text Int])
insertOrRetrieveArg h sz argMaps = case argMaps of
  [] -> error "panic: empty function nesting" --impossible
  mp:xs -> case asum (M.lookup h <$> xs) of
    Just x        -> (Right x, argMaps)
    Nothing       -> case il h sz mp of
      (Just x, _) -> (Right x , argMaps)
      (_, mp')    -> (Left sz , mp':xs)

pd = moduleWIP . parseDetails
addArgName , addBindName , addUnknownName:: Text -> Parser IName
addArgName    h = do
  n <- use (moduleWIP . parseDetails . nArgs)
  pd . hNameArgs %%= insertOrRetrieveArg h n >>= \case
    Left _sz -> moduleWIP . parseDetails . nArgs <<%= (1+)
    Right  x -> pure x

-- search (local let bindings) first, then the main bindMap
addBindName   h = do
  n <- use (moduleWIP . parseDetails . hNameBinds . _1)
  r <- use (moduleWIP . parseDetails . hNameLocals) >>= \case
    [] -> pd . hNameBinds  %%= insertOrRetrieveSZ h
    _  -> pd . hNameLocals %%= insertOrRetrieveArg h n
  case r of
    Right r -> fail $ toS $ "Binding overwrites existing binding: '" <> h <> "'"
    Left  r -> pure r

eitherOne = \case { Right r -> r ; Left r -> r }
addAnonBindName = (moduleWIP . parseDetails . hNameBinds . _1 <<%= (+1))
addUnknownName h = eitherOne <$> (pd . hNamesNoScope %%= insertOrRetrieve h)

newFLabel h    = eitherOne <$> (moduleWIP . parseDetails . fields %%= insertOrRetrieve h)
newSLabel h    = eitherOne <$> (moduleWIP . parseDetails . labels %%= insertOrRetrieve h)
lookupSLabel h = (M.!? h) <$> use (moduleWIP . parseDetails . labels)

lookupBindName h = use (moduleWIP . parseDetails) >>= \p -> let
  tryArg = case p ^. hNameArgs of
    [] -> pure $ Nothing
    thisFrame : prevFrames -> case thisFrame M.!? h of
      Just n  -> pure $ Just $ VLocal n
      Nothing -> case asum $ (M.!? h) <$> prevFrames of
        Just upStackArg -> do
          moduleWIP .parseDetails .freeVars %= (IS.insert upStackArg)
          pure $ Just $ VLocal upStackArg
        Nothing -> pure Nothing
  tryLet = VBind  <$> (asum $ (M.lookup h) `map` (p ^. hNameLocals))
  tryTop = VBind  <$> M.lookup h (p ^. hNameBinds . _2)
  in tryArg >>= \arg -> Var <$> case choice [arg , tryLet , tryTop] of
    Just i  -> pure i
    Nothing -> VExtern <$> addUnknownName h

-- function defs add a layer of lambda-bound arguments , same for let
getFreeVars = do
  free <- use (moduleWIP . parseDetails . freeVars)
  ars  <- fromJust . head <$> use (moduleWIP . parseDetails . hNameArgs)
  let free' = foldr IS.delete free (M.elems ars)
  moduleWIP . parseDetails . freeVars .= free'
  pure free'

incLetNest = moduleWIP . parseDetails . hNameLocals %= (M.empty :)
decLetNest = moduleWIP . parseDetails . hNameLocals %= drop 1
newArgNest p = let
  incArgNest = moduleWIP . parseDetails . hNameArgs %= (M.empty :)
  decArgNest = moduleWIP . parseDetails . hNameArgs %= drop 1
  in incArgNest *> p <* decArgNest
withTmpReserved ms p = (tmpReserved %= (ms :)) *> p <* (tmpReserved %= drop 1)

lookupImplicit :: Text -> Parser IName -- implicit args
lookupImplicit h = do
  pd <- use $ moduleWIP . parseDetails
  case asum $ map (M.!? h) (pd ^. hNameArgs) of
    Just arg -> pure $ arg
    Nothing  -> fail ("Not in scope: implicit arg '" ++ (T.unpack h) ++ "'")

-----------
-- Lexer --
-----------
-- A key convention: tokens consume trailing whitespace (using `symbol` or `lexeme`)
-- so parsers can assume they start on a non-blank.
-- Space consumers: scn eats newlines, sc does not. Make sure to save newline offsets
addNewlineOffset :: Parser ()
addNewlineOffset = getOffset >>= \o -> moduleWIP . parseDetails . newLines %= (o - 1 :)
isHSpace x = isSpace x && x /= '\n' -- isHSpace , but handles all unicode spaces
sc  :: Parser () = L.space (void $ takeWhile1P (Just "white space") isHSpace) lineComment blockComment
scn :: Parser () = let
  space1 = sc *> some endLine *> space
  space  = skipMany (sc *> endLine)
  in L.space space1 lineComment blockComment
endLine = lexeme (single '\n') <* addNewlineOffset
lineComment = L.skipLineComment "--" -- <* addNewlineOffset
blockComment = let -- still need to count newlines
  skipBlockComment start end = string start
    *> manyTill (endLine {-<|> blockComment nested-} <|> anySingle) end
  in void $ skipBlockComment "{-" "-}"

lexeme, lexemen :: Parser a -> Parser a -- parser then whitespace
[lexeme, lexemen]   = L.lexeme <$> [sc , scn]
symbol, symboln :: Text -> Parser Text --verbatim strings
[symbol , symboln]  = L.symbol <$> [sc , scn]

parens, braces, bracesn , brackets , bracketsn :: Parser a -> Parser a
parens    = symbol  "(" `between` symbol  ")"
braces    = symbol  "{" `between` symbol  "}"
bracesn   = symboln "{" `between` symboln "}"
brackets  = symbol  "[" `between` symbol  "]"
bracketsn = symboln "[" `between` symboln "]"
p `sepBy2` sep = (:) <$> p <*> (some (sep *> p))

-----------
-- Names --
-----------
reservedChars = ".'@(){};,\\\""
reservedNames = S.fromList $ words "set over type data record class extern externVarArg let rec in where case \\case of _ import require \\ : :: = ? | λ =>"
-- check the name isn't an iden which starts with a reservedWord
reservedName w = (void . lexeme . try) (string w *> notFollowedBy idenChars)
reservedChar c
  | T.any (==c) reservedChars = lexeme (char c)
  | otherwise = lexeme ((char c) <* notFollowedBy idenChars)
reservedOp = reservedName
reserved = reservedName
isIdenChar x = not (isSpace x) && not (T.any (==x) reservedChars)
idenChars = takeWhile1P Nothing isIdenChar
checkReserved x = if x `S.member` reservedNames
  then fail $ "keyword '" <> toS x <> "' cannot be an identifier"
  else pure x
checkLiteral x = if isDigit `T.all` x -- TODO not good enough (1e3 , 2.0 etc..)
  then fail $ "literal: '" <> toS x <> "' cannot be an identifier"
  else pure x
checkIden = checkReserved <=< checkLiteral

-- We must use 'try', to backtrack if we parse a reserved word
iden :: Parser HName = lexeme . try $ (idenChars >>= checkIden)
idenNo_ = lexeme idenNo_'
idenNo_' = try $ (takeWhile1P Nothing (\x->isIdenChar x && x /= '_') >>= checkIden)

-- separated and split on '_' (ie. argument holes)
pMixfixWords :: Parser [Maybe Text] = lexeme $ do
  some (choice [Nothing <$ char '_' , Just <$> idenNo_']) >>= \case
    [Nothing] -> fail "'_' cannot be an identifier"
    mf -> pure mf
-- exported convenience function for use by builtins (Externs.hs)
parseMixFixDef :: Text -> Either (ParseErrorBundle Text Void) [Maybe Text]
 = \t -> runParserT pMixfixWords "<internal>" t `evalState` _

-- ref = reference indent level
-- lvl = lvl of first indented item (often == pos)
indentedItems prev scn p finished = let
 go lvl = scn *> do
  pos <- L.indentLevel
  [] <$ lookAhead (eof <|> finished) <|> if
     | pos <= prev -> pure []
     | pos == lvl  -> (:) <$> p <*> go lvl
     | otherwise   -> fail $ "incorrect indentation, got " <> show pos <> ", expected <= " <> show prev <> " or == " <> show lvl
     -- L.incorrectIndent EQ lvl pos
 in L.indentLevel >>= go

 -- tells linefold and let-ins not to eat our indentedItems
svIndent = L.indentLevel >>= (indent .=)

linefold p = let
  doLinefold = endLine *> scn *> do
    prev <- use indent
    cur  <- L.indentLevel
    when (prev >= cur)
      (fail $ "not a linefold " <> show prev <> ", expected >= " <> show cur)
--    (L.incorrectIndent GT prev cur) (alas GEQ is not an Ordering)
    indent .= cur
    p -- <* (indent .= prev)
    <* lookAhead endLine -- make sure this was a linefold to not corrupt error messages
  in try doLinefold <|> p

------------
-- Parser --
------------
parseModule :: FilePath -> Text -> Either (ParseErrorBundle Text Void) Module
  = \nm txt ->
  let startModule = Module {
          _moduleName  = T.pack nm
        , _imports     = []
        , _externFns   = []
        , _bindings    = []
        , _parseDetails = ParseDetails {
             _hNameBinds    = (0 , M.empty)
           , _hNameMFWords  = (0 , M.empty)
           , _hNameArgs     = [] -- stack of lambda-bounds
           , _hNameLocals   = []
           , _freeVars      = IS.empty
           , _nArgs         = 0
           , _hNamesNoScope = M.empty -- M.fromList [("->",0)]-- M.empty
           , _fields        = M.empty
           , _labels        = M.empty
           , _newLines      = []
        }
      }
      end = (bindings %~ reverse)
  in end <$> runParserT (scn *> doParse *> eof *> use moduleWIP) nm txt
  `evalState` ParseState {
       _indent      = mkPos 1
     , _moduleWIP   = startModule
     , _tmpReserved = []
     , _piBound     = []
     }

-- group declarations as they are parsed
doParse = void $ decl `sepEndBy` (optional endLine *> scn) :: Parser ()
decl = svIndent *> choice
   [ reserved "import" *> (iden >>= addImport)
   , extern
   , void (funBind LetOrRec) <?> "binding"
   , bareTT <?> "repl expression"
   ]

-- for the repl
bareTT = addAnonBindName *> ((\tt -> addBind (FunBind $ FnDef "replExpr" LetOrRec Nothing [] IS.empty [FnMatch [] [] tt] Nothing)) =<< tt)

extern =
 let _typed = reservedOp ":" *> tt
     doName = iden >>= \hNm -> addBindName hNm *> pure hNm
 in addExtern =<< choice
 [ Extern   <$ reserved "extern"      <*> doName <*> _typed
 , ExternVA <$ reserved "externVarArg"<*> doName <*> _typed
 ]

-------------------
-- Function defs --
-------------------
mixFix2Nm = T.concat . map (\case { Just nm->nm ; Nothing->"_" })
parsePrec = let
  assoc = choice [Assoc <$ single 'a' , AssocRight <$ single 'r' , AssocLeft <$ single 'l' , AssocNone <$ single 'n']
  in lexeme $ Prec
  <$> (assoc     <?> "assoc : [a | l | r | n]")
  <*> (L.decimal <?> "precedence (an integer)")

addMixfixWords m mfBind mfdef = let
  addMFParts mfp = mfp `forM` \case
    Just hNm -> Just <$> addMFWord hNm MFPart
    Nothing  -> pure Nothing
  in case m of
    Just hNm           : mfp -> addMFWord hNm (StartPrefix mfdef)
      >>= \w -> (Just w :) <$> addMFParts mfp
    Nothing : Just hNm : mfp -> addMFWord hNm (StartPostfix mfdef)
      >>= \w -> (Nothing :) . (Just w :) <$> addMFParts mfp

funBind letRecT = lexeme pMixfixWords >>= \case
  [Just nm] -> VBind <$> funBind' letRecT nm Nothing (symbol nm *> many (lexeme singlePattern))
  mfdefHNames -> let
    pMixFixArgs = \case
      []            -> pure []
      Just  nm : x -> symbol nm *> pMixFixArgs x
      Nothing  : x -> (:) <$> lexeme singlePattern <*> pMixFixArgs x
    in mdo
    prec <- fromMaybe (defaultPrec) <$> optional (braces parsePrec)
    let hNm = mixFix2Nm mfdefHNames
    mfdefINames <- addMixfixWords mfdefHNames iNm mfdef
    let mfdef = MixfixDef iNm mfdefINames prec
    iNm <- funBind' letRecT (mixFix2Nm mfdefHNames) (Just mfdef) (pMixFixArgs mfdefHNames)
    pure (VBind iNm)

funBind' :: LetRecT -> Text -> Maybe MixfixDef -> Parser [Pattern] -> Parser IName
funBind' letRecT nm mfDef pMFArgs = newArgNest $ mdo
  iNm <- addBindName nm -- handle recursive references
    <* addBind (FunBind $ FnDef nm letRecT mfDef (implicits ++ pi) free eqns ty)
  ars <- many singlePattern
  ann <- tyAnn
  let (implicits , ty) = case ann of { Just (i,t) -> (i,Just t) ; _ -> ([],Nothing) }
  (pi , eqns) <- getPiBounds $ choice
    [ (:[]) <$> fnMatch (pure ars) (reserved "=") -- (FnMatch [] ars <$> (lexemen (reservedOp "=") *> tt))
    , case (ars , ann) of
        ([] , Just{})  -> some $ try (endLine *> fnMatch pMFArgs (reserved "=") )
        (x  , Just{})  -> fail "TODO no parser for: fn args followed by type signature"
--      (x  , Nothing) -> fail $ "found pattern with no binding: " <> show x
        (x  , Nothing) -> some $ try (endLine *> fnMatch pMFArgs (reserved "=") )
    ]
  free <- getFreeVars
  pure iNm

tyAnn :: Parser (Maybe ([ImplicitArg] , TT)) = let
    implicitArg = (,) <$> (iden >>= addArgName) <*> optional (reservedChar ':' *> tt)
  in newArgNest $ do
  optional (reserved "::" *> bracesn (implicitArg `sepBy` reserved ";")) >>= \case
    Just implicits -> fmap (implicits,) <$> optional (reservedChar ':' *> tt)
    Nothing        -> fmap ([],)        <$> optional (reservedChar ':' *> tt)

-- TODO sadly will have to generalise this using levels anyway
--lambda = reservedChar '\\' *> (Var . VBind <$> addAnonBindName) <* do
--  newArgNest $ mdo
--    addBind $ FunBind $ FnDef "lambda" Let Nothing [] free eqns Nothing
--    eqns <- (:[]) <$> fnMatch (many pattern) (reserved "=>")
--    free <- getFreeVars
--    pure ()

lambda = reservedChar '\\' *> do
  newArgNest $ do
    eqns <- (:[]) <$> fnMatch (many singlePattern) (reserved "=>")
    free <- getFreeVars
    pure $ Abs $ FunBind $ FnDef "lambda" LetOrRec Nothing [] free eqns Nothing

fnMatch pMFArgs sep = -- sep is "=" or "=>"
  -- TODO is hoistLambda ideal here ?
  let hoistLambda = try $ lexemen sep *> reservedChar '\\' *> notFollowedBy (string "case") *> newArgNest (fnMatch (many singlePattern) (reserved "=>"))
      normalFnMatch = FnMatch [] <$> (pMFArgs <* lexemen sep) <*> tt
  in choice [ hoistLambda , normalFnMatch ]

-- TT parser
ttArg , tt :: Parser TT
(ttArg , tt) = (arg , anyTT)
  where
  anyTT = (match <|> appOrArg) >>= typedTT <?> "tt"
  argOrLens = arg >>= \larg -> option larg (lens larg) -- lens bind tighter than App
  appOrArg = getOffset >>= \o -> argOrLens >>= \larg -> option larg
    ( case larg of
--     Lit l -> LitArray . (l:) <$> some (lexeme $ try (literalP <* notFollowedBy iden))
--     -- Breaks `5 + 5`
       P.Label l [] -> P.Label l <$> some arg
       fn -> choice
         [ Juxt o . (fn:) <$> some (linefold argOrLens)
         , pure fn
         ]
    )--  >>= \tt -> option tt (lens tt)
  lens :: TT -> Parser TT
  lens record = let
    lensNext path = getOffset >>= \o -> reservedChar '.' *> choice [
        TTLens o record (reverse path) <$> (LensSet  <$ reserved "set"  <*> arg)
      , TTLens o record (reverse path) <$> (LensOver <$ reserved "over" <*> arg)
      , idenNo_ >>= newFLabel >>= \p -> choice [lensNext (p : path) , pure (TTLens o record (reverse (p:path)) LensGet)]
      ]
    in lensNext []
  arg = choice
   [ reserved "_" $> WildCard
   , lambdaCase -- "\\case"
   , lambda     -- "\"
   , letIn
-- , match      -- "case"
-- , tySum      -- "|"
   , con
   , Lit <$> (lexeme $ try (literalP <* notFollowedBy iden))
   , try $ idenNo_ >>= \x -> choice [label x , lookupBindName x] -- varName -- incl. label
   , try $ iden >>= lookupBindName -- holey names used as defined
   , TyListOf <$> brackets tt
   , parens $ choice [try piBinder , (tt >>= typedTT) , scn $> Cons []]
   , P.List <$> brackets (tt `sepBy` reservedChar ',' <|> (scn $> []))
   ] <?> "ttArg"
  label i = lookupSLabel i >>= \case
    Nothing -> P.Label <$ reservedOp "@" <*> newSLabel i <*> (many arg)
    Just l  -> pure $ P.Label l [] -- <$> many arg (converted in App)

  tySum = TySum <$> let
    labeledTTs = do
      hLabel <- iden
      label  <- newSLabel hLabel
      getPiBounds tyAnn >>= \case
        (pis , Nothing) -> fail $ "sumtype constructor '" <> T.unpack hLabel <> "' needs a type annotation"
        (pis , Just (impls , ty)) -> pure (label , pis ++ impls , ty)
    in some $ try (scn *> (reservedChar '|' *> lexeme labeledTTs))

  con = let
    fieldAssign = (,) <$> (iden >>= newFLabel) <* reservedOp "=" <*> tt
    conHash = do
      string "##"
      ref <- use indent <* scn
      indentedItems ref scn fieldAssign (fail "")
    conBraces = braces (fieldAssign `sepBy` reservedChar ',')
    in Cons <$> (conHash <|> conBraces)

  caseSplits = Match <$> let
    split = newArgNest $ do
      svIndent
      lName <- iden >>= newSLabel
      optional (reservedChar '@')
      pats <- many singlePattern
      reserved "=>"
      splitFn <- tt
      free <- getFreeVars
      pure (lName , free , pats , splitFn)
--  in choice [some $ try (scn *> reservedChar '|' *> split) , pure <$> split]
    in do
      ref <- use indent <* scn
      L.indentLevel >>= \i -> case compare i ref of
        LT -> fail "new case should not be less indented than reference indent"
        _  -> indentedItems ref scn split (fail "")
  match = reserved "case" *> do
    scrut  <- tt
    reserved "of"
    (`App` [scrut]) <$> caseSplits

  lambdaCase = reserved "\\case" *> caseSplits

  letIn = let
    pletBinds letStart (letRecT :: LetRecT) = (\p -> incLetNest *> p <* decLetNest) $ do
      scn -- go to first indented binding
      ref <- use indent
      svIndent -- tell linefold (and subsequent let-ins) not to eat our indentedItems
      traceShowM ref
      indentedItems ref scn (funBind letRecT) (reserved "in") <* reserved "in"
      tt
    in do
      letStart <- use indent -- <* scn
      inExpr <- (reserved "let" *> pletBinds letStart Let)
            <|> (reserved "rec" *> pletBinds letStart Rec)
      pure inExpr

  typedTT exp = tyAnn >>= \case --optional type annotation is parsed as anonymous let-binding
    Nothing -> pure exp
    Just ([] , WildCard)  ->  pure exp -- don't bother if no info given (eg. pi binder)
    Just (implicits , ty) -> case exp of
      Var (VLocal l) -> addPiBound (l , Just ty) *> pure exp
      x -> (Var . VBind <$> addAnonBindName)
        <* addBind (FunBind $ FnDef "_:" LetOrRec Nothing [] IS.empty [FnMatch [] [] exp] (Just ty))

  piBinder = do
    i <- iden
    lookAhead (void (reservedChar ':') <|> reservedOp "::")
    (Var . VLocal <$> addArgName i) >>= typedTT

-- TODO parse patterns as TT's to handle pi-bound arguments
pattern = choice
  [ try iden >>= \i -> addArgName i >>= \a -> choice
     [ some singlePattern >>= \args -> lookupSLabel i >>=
         maybe (newSLabel i) pure <&> \f -> PComp a (PLabel f args)
     , loneIden a i
     ]
  , singlePattern
  ]

loneIden a i = lookupSLabel i <&> \case
  Nothing -> PArg a
  Just  l -> PComp a (PLabel l [])

singlePattern = choice
 [ try iden >>= \i -> addArgName i >>= \a -> loneIden a i
 , parens pattern
 , addArgName "" >>= \a -> PComp a <$> choice
   [ let fieldPattern = iden >>= \iStr -> newFLabel iStr >>= \i -> (i,) <$> choice
           [ reservedOp "=" *> pattern
           , PArg <$> addArgName iStr -- { A } pattern is same as { A=A }
           ]
     in PCons <$> braces (fieldPattern `sepBy` reservedChar ',')
   , PWildCard <$ reserved "_"
   , PLit <$> try literalP
   ]
 ]

---------------------
-- literal parsers --
---------------------
literalP = let
  signed p = let
    sign :: Bool -> Parser Bool = \i -> option i $ (single '+' *> sign i) <|> (single '-' *> sign (not i))
    in sign False >>= \s -> p <&> \n -> if s then negate n else n
  -- L.charLiteral handles escaped chars (eg. \n)
  char :: Parser Char = between (single '\'') (single '\'') L.charLiteral
  stringLiteral :: Parser [Char] = choice
    [ single '\"'       *> manyTill L.charLiteral (single '\"')
    , (string "\"\"\"") *> manyTill L.charLiteral (string "\"\"\"")
    , (string "''")     *> manyTill L.charLiteral (string "''")
    , (string "$")      *> manyTill L.charLiteral endLine]
  intLiteral = choice
    [ try (signed L.decimal)
    , string "0b" *> L.binary
    , string "0x" *> L.hexadecimal
    , string "0o" *> L.octal
    ]
 in choice
   [ Char   <$> char
   , String <$> stringLiteral
   , Int    <$> intLiteral
   , numP
   ] <?> "literal"

decimal_ , dotDecimal_ , exponent_ :: Parser Text
decimal_    = takeWhile1P (Just "digit") isDigit
dotDecimal_ = char '.' *> decimal_
exponent_   = char' 'e' *> decimal_

numP :: Parser Literal = do
  c <- decimal_
  f <- option T.empty dotDecimal_
  e <- option T.empty exponent_
  pure $ if T.null f && T.null e
    then PolyInt c
    else PolyFrac $ c `T.snoc` '.' `T.append` f `T.append` e
