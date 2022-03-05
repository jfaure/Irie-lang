module Parser (parseModule , parseMixFixDef) where
-- Parsing converts all text names to ints and doesn't require importing or reading other modules
--   1. VBind:   top-level let bindings
--   2. VLocal:  lambda-bound arguments
--   3. VExtern: out-ofscope HNames inamed now and resolved later
-- * name scope is checked and free variables are noted:
-- * we cannot resolve externs (incl forward refs) or mixfixes yet.
--
-- Note: add corresponding bind immediately after adding an IName (can resort to recursiveDo)
-- 3 parts: Module builder + parse state (scoping, free vars, desugaring), Lexing , Parsing

import Prim
import ParseSyntax as P
import MixfixSyn
--import DesugarParse
import Text.Megaparsec-- hiding (State)
import Text.Megaparsec.Char
import System.FilePath.Posix as FilePath (dropExtension , takeFileName)
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad (fail)
import Control.Lens
--import qualified Text.Megaparsec.Debug as DBG
dbg i = identity -- DBG.dbg i

showN n = try ((takeP Nothing n >>= traceShowM) *> fail "debug parser") <|> pure () :: Parser ()

type Parser = ParsecT Void Text (Prelude.State ParseState)

--------------------------
-- Parsestate functions --
--------------------------
addBind b     = moduleWIP . bindings   %= (b:)
addImport i   = moduleWIP . imports    %= (i:)
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

-- The trickiness below is due to insertLookup, which saves a log(n) operation
il = M.insertLookupWithKey (\k new old -> old)
-- Data.Map's builtin size is good enough for labels/fields
insertOrRetrieve h mp = let sz = M.size mp in case il h sz mp of
  (Just x, mp) -> (Right x  , mp)
  (_,mp)       -> (Left  sz , mp)
-- use a custom size variable to track bind count since anonymous binds aren't in the map
insertOrRetrieveSZ h (sz,mp) = case il h sz mp of
  (Just x, mp) -> (Right x , (sz,mp))
  (_,mp)       -> (Left sz , (sz+1,mp))
-- the list of args corresponds to a nest of function defs
-- if we're adding an argument, we do so to the first (innermost) level
insertOrRetrieveArg :: Text -> Int -> [M.Map Text Int] -> (Either Int Int, [M.Map Text Int])
insertOrRetrieveArg h sz argMaps = case argMaps of
  [] -> error "panic: empty function nesting" --impossible
  mp:xs -> case asum (M.lookup h <$> xs) of
    Just x        -> (Right x, argMaps)
    Nothing       -> case il h sz mp of
      (Just x, _) -> (Right x , argMaps)
      (_, mp')    -> (Left sz , mp':xs)

pd = moduleWIP . parseDetails
addAnonArgName = moduleWIP . parseDetails . nArgs <<%= (1+)
addArgName , addNewArgName , addBindName , addUnknownName :: Text -> Parser IName
addArgName    h = do
  n <- use (moduleWIP . parseDetails . nArgs)
  pd . hNameArgs %%= insertOrRetrieveArg h n >>= \case
    Left _sz -> moduleWIP . parseDetails . nArgs <<%= (1+)
    Right  x -> pure $ x
addNewArgName h = do
  n <- moduleWIP . parseDetails . nArgs <<%= (1+)
  moduleWIP . parseDetails . hNameArgs %= (\(x:xs) -> M.insert h n x : xs)
  pure n

-- register an '_'; so () and funBind can make an implicit abstraction
addUnderscoreArg i = Var (VLocal i) <$ (moduleWIP . parseDetails . underscoreArgs %= (`setBit` i))

-- search (local let bindings) first, then the main bindMap
addBindName   h = do
  n <- use (moduleWIP . parseDetails . hNameBinds . _1)
  r <- use (moduleWIP . parseDetails . hNameLocals) >>= \case
    [] -> pd . hNameBinds  %%= insertOrRetrieveSZ h
    _  -> (pd . hNameLocals %%= insertOrRetrieveArg h n) <* addAnonBindName -- inc the sz counter
  case r of
    Right r -> fail $ toS $ "Binding overwrites existing binding: '" <> h <> "'"
    Left  r -> pure r

eitherOne = \case { Right r -> r ; Left r -> r }
addAnonBindName = (moduleWIP . parseDetails . hNameBinds . _1 <<%= (+1))
addUnknownName h = eitherOne <$> (pd . hNamesNoScope %%= insertOrRetrieve h)

newFLabel h    = eitherOne <$> (moduleWIP . parseDetails . fields %%= insertOrRetrieve h)
newSLabel h    = eitherOne <$> (moduleWIP . parseDetails . labels %%= insertOrRetrieve h)
lookupSLabel h = (M.!? h) <$> use (moduleWIP . parseDetails . labels)

-- a Name may be an arg, or another binding in scope at some let-depth
lookupBindName h = use (moduleWIP . parseDetails) >>= \p -> let
  tryArg = case p ^. hNameArgs of
    [] -> pure $ Nothing
    thisFrame : prevFrames -> case thisFrame M.!? h of
      Just n  -> pure $ Just $ VLocal n
      Nothing -> case asum $ (M.!? h) <$> prevFrames of
        Just upStackArg -> do
          moduleWIP .parseDetails . freeVars %= (`setBit` upStackArg)
          pure $ Just $ VLocal upStackArg
        Nothing -> pure Nothing
  tryLet = VBind  <$> (asum $ (M.lookup h) `map` (p ^. hNameLocals))
  tryTop = VBind  <$> M.lookup h (p ^. hNameBinds . _2)
  in tryArg >>= \arg -> Var <$> case choice [arg , tryLet , tryTop] of
    Just i  -> pure i
    Nothing -> VExtern <$> addUnknownName h

-- The names nest tracks the scope of local definitions
newLetNest p = (moduleWIP . parseDetails . hNameLocals %= (M.empty :))
               *> p <* (moduleWIP . parseDetails . hNameLocals %= drop 1)

getFreeVars = use (moduleWIP . parseDetails . freeVars)

-- Add an argMap to the argMaps stack and compute freeVars when this new nest returns
newArgNest :: Parser a -> Parser (a , FreeVars)
newArgNest p = let
  incArgNest = moduleWIP . parseDetails . hNameArgs %= (M.empty :)
  decArgNest = moduleWIP . parseDetails . hNameArgs %= drop 1
  in do
    incArgNest
    ret <- p
    -- freeVars is freeVars minus args introduced at this nest
    ourArgs <- fromJust . head <$> use (moduleWIP . parseDetails . hNameArgs)
    free    <- moduleWIP . parseDetails . freeVars <%= (\oldFree -> foldr (flip clearBit) oldFree (M.elems ourArgs))
    decArgNest
    pure (ret , free)

lookupImplicit :: Text -> Parser IName -- implicit args
lookupImplicit h = do
  pd <- use $ moduleWIP . parseDetails
  case asum $ map (M.!? h) (pd ^. hNameArgs) of
    Just arg -> pure $ arg
    Nothing  -> fail ("Not in scope: implicit arg '" <> toS h <> "'")

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
sc  :: Parser () = L.space (void $ takeWhile1P (Just "white space") isHSpace) lineComment blockComment
scn :: Parser () = let
  space1 = sc *> some endLine *> skipMany (sc *> endLine)
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
reservedChars = ".@(){};:,\\\""
reservedNames = S.fromList $ words "let rec in \\case case as over foreign foreignVarArg where of _ module import require = ? | λ =>"
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

-- We must use 'try', to backtrack if we ended up parsing a reserved word
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
 -- 'fail' here to backtrack the whitespace/newlines. Otherwise the App parser sees and eats things from later lines
    | pos <= prev -> fail $ ("end of indent: " <> show pos <> " <= " <> show prev)
    | pos == lvl  -> p >>= \ok -> option [ok] ((ok :) <$> try (go lvl))
    | otherwise   -> fail ("incorrect indentation, got " <> show pos <> ", expected <= " <> show prev <> " or == " <> show lvl)
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
--  indent .= cur
    p -- <* (indent .= prev)
    <* lookAhead (single '\n') -- make sure this was a linefold to not corrupt error messages
  in try doLinefold <|> p

------------
-- Parser --
------------
parseModule :: FilePath -> Text -> Either (ParseErrorBundle Text Void) Module
  = \nm txt -> let
  startModule = Module {
      _moduleName  = Left (toS (dropExtension $ takeFileName nm))
    , _functor     = Nothing
    , _imports     = []
    , _bindings    = []
    , _parseDetails = ParseDetails {
        _hNameBinds     = (0 , M.empty)
      , _hNameMFWords   = (0 , M.empty)
      , _hNameArgs      = [] :: [M.Map HName IName] -- stack of lambda-bounds
      , _hNameLocals    = [] :: [M.Map HName IName]
      , _freeVars       = emptyBitSet
      , _nArgs          = 0
      , _underscoreArgs = 0 :: BitSet
      , _hNamesNoScope  = M.empty -- track VExterns
      , _fields         = M.empty -- field names
      , _labels         = M.empty -- explicit label names; note. `L a` is ambiguous
      , _newLines       = []
    }
  }
  end = (bindings %~ reverse)
  in end <$> runParserT (scn *> doParse *> eof *> use moduleWIP) nm txt
  `evalState` ParseState {
       _indent      = mkPos 1
     , _moduleWIP   = startModule
     , _piBound     = []
     }

-- group declarations as they are parsed
doParse = void $ decl `sepEndBy` (optional endLine *> scn) :: Parser ()
decl = svIndent *> choice
   [ reserved "import" *> (iden >>= addImport)
   , void functorModule
   , pForeign
   , void (funBind True LetOrRec) <?> "binding"
-- , bareTT <?> "repl expression"
   ] <?> "import , extern or local binding"

--bareTT = addAnonBindName *> ((\tt -> addBind (FnDef "replExpr" LetOrRec Nothing 0 [FnMatch [] tt] Nothing)) =<< tt)

pForeign = do -- external function defined outside of Irie and opaque until link-time
  fn  <- ((Foreign <$ reserved "foreign") <|> (ForeignVA <$ reserved "foreignVA"))
  hNm <- iden
  addBindName hNm
  ty <- reservedOp ":" *> tt
  addBind (FnDef hNm Let Nothing 0 (FnMatch [] (Foreign hNm ty) :| []) (Just ty))

functorModule :: Parser ()
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
      >>= \w -> (Just w : )              <$> addMFParts mfp
    Nothing : Just hNm : mfp -> addMFWord hNm (StartPostfix mfdef)
      >>= \w -> (Nothing :) . (Just w :) <$> addMFParts mfp

funBind isTop letRecT = (<?> "binding") $ optional (reserved "rec") *> lexeme pMixfixWords >>= \case
  [Just nm] -> let pArgs = many (lexeme singlePattern) -- non-mixfix fn def can parse args immediately
    in VBind <$> funBind' isTop pArgs letRecT nm Nothing (symbol nm *> pArgs)
  mfdefHNames -> let
    hNm = mixFix2Nm mfdefHNames
    pMixFixArgs = \case
      []           -> pure []
      Just  nm : x -> symbol nm *> pMixFixArgs x
      Nothing  : x -> (:) <$> lexeme singlePattern <*> pMixFixArgs x
    in mdo
    prec <- fromMaybe defaultPrec <$> optional (braces parsePrec)
    mfdefINames <- addMixfixWords mfdefHNames iNm mfdef
    let mfdef = MixfixDef iNm mfdefINames prec
    iNm <- funBind' isTop (pure []) letRecT (mixFix2Nm mfdefHNames) (Just mfdef) (pMixFixArgs mfdefHNames)
    pure (VBind iNm)

some1 f = (:|) <$> f <*> many f

-- parse a function definition (given a possible mixfix pattern parsed in the type annotation)
-- => pMFArgs should be used to parse extra equations on subsequent lines
-- If this is a mixfix, args will be [] at this point
funBind' :: Bool -> Parser [Pattern] -> LetRecT -> Text -> Maybe MixfixDef -> Parser [Pattern] -> Parser IName
funBind' isTop pArgs letRecT nm mfDef pMFArgs = (<?> "function body") $ mdo
  iNm <- addBindName nm -- add in mfix in case of recursive references
    <* addBind (FnDef nm letRecT mfDef free eqns ann)
  ((eqns , ann) , free) <- newArgNest $ do
    ann  <- optional tyAnn
    eqns <- choice -- TODO maybe don't allow `_+_ a b = add a b`
--    [ (:|) <$> (fnMatch pArgs (reserved "=")) <*> many (try (endLine *> fnMatch pMFArgs (reserved "=")))
      [ (:|) <$> (fnMatch pArgs (reserved "="))
             <*> many (try $ endLine *> scn *> svIndent *> fnMatch pMFArgs (reserved "="))
      , case ([] , ann) of
          (x  , Nothing) -> some1 $ try (endLine *> fnMatch pMFArgs (reserved "=") ) -- f = _
          ([] , Just{})  -> some1 $ try (endLine *> fnMatch pMFArgs (reserved "=") ) -- f : T = _
--        (x  , Just{})  -> fail  $ "Expected function definition \" = _\" , got type annotation \" : _\"" -- f x : _
      ]
    pure (eqns , ann)
  pure iNm

tyAnn :: Parser TT = do {-newArgNest $-}
  reservedChar ':'
  (pi , ty) <- getPiBounds tt
  -- no freeVars in a pi-binder
  pure $ case pi of
    [] -> ty
    pi -> Abs (FnDef "pi-binder" LetOrRec Nothing emptyBitSet (FnMatch (PPi <$> pi) ty :| []) Nothing)

lambda = do
  (eqns , free) <- newArgNest $ (:|[]) <$> fnMatch (many singlePattern) (reserved "=>")
  pure $ Abs $ FnDef "lambda" LetOrRec Nothing free eqns Nothing

fnMatch pMFArgs sep = -- sep is "=" or "=>"
  -- TODO is hoistLambda ideal here ? (idea is to merge abs `f x = \y => _` into f x y = _
  let hoistLambda = try $ lexemen sep *> reservedChar '\\' *> notFollowedBy (string "case")
        *> (fnMatch (many singlePattern)) (reserved "=>")
      normalFnMatch = FnMatch <$> (pMFArgs <* lexemen sep) <*> tt
  in {-hoistLambda <|>-} normalFnMatch -- TODO reactivate

-- make a lambda around any '_' found within the tt eg. `(_ + 1)` => `\x => x + 1`
catchUnderscoreAbs :: TT -> Parser TT
catchUnderscoreAbs tt = use (moduleWIP . parseDetails . underscoreArgs) >>= \underscores ->
  if 0 == underscores then pure tt else
  let eqns = FnMatch (PArg <$> bitSet2IntList underscores) tt :| []
  in do
    free <- getFreeVars -- Freevars are exactly those in the parse state, since we introduced none of them at this new Abs
    Abs (FnDef "_abs" LetOrRec Nothing free eqns Nothing) <$ (moduleWIP . parseDetails . underscoreArgs .= 0)

-- TT parser
ttArg , tt :: Parser TT
(ttArg , tt) = (arg , anyTT)
  where
  anyTT = ({-tySum <|>-} appOrArg) >>= catchUnderscoreAbs >>= typedTT <?> "tt"
   -- lens bind tighter than App
  argOrLens = arg       >>=                     \larg -> option larg (lens larg)
  appOrArg  = getOffset >>= \o -> argOrLens >>= \larg -> option larg $ case larg of
--  Lit l -> LitArray . (l:) <$> some (lexeme $ try (literalP <* notFollowedBy iden)) -- Breaks `5 + 5`
    P.Label l [] -> P.Label l <$> some (linefold argOrLens) --arg
    fn -> (Juxt o . (fn:) <$> some (linefold argOrLens))
  lens :: TT -> Parser TT
  lens record = let
    lensNext path = getOffset >>= \o -> reservedChar '.' *> choice [
        TTLens o record (reverse path) <$> (LensSet  <$ reserved "set"  <*> arg)
      , TTLens o record (reverse path) <$> (LensOver <$ reserved "over" <*> arg)
      , idenNo_ >>= newFLabel >>= \p -> choice [lensNext (p : path) , pure (TTLens o record (reverse (p:path)) LensGet)]
      ]
    in lensNext []
  arg = use indent >>= \sv -> choice
   [ reserved "_" *> (addAnonArgName >>= addUnderscoreArg)
   , reserved "?" $> WildCard
   , letIn
   , reserved "\\case" *> caseSplits
   , (reservedChar '\\' <|> reservedChar 'λ') *> lambda
   , reserved "do" *> doExpr
   , reserved "case"   *> match
   , reserved "record" *> tyRecord  -- multiline record decl
   , reserved "data"   *> tySumData -- multiline sumdata decl
-- , piBinder *> arg
   , con
   , Lit <$> lexeme (try (literalP <* notFollowedBy iden)) -- must be before Iden parsers
   , try $ idenNo_ >>= \x -> choice [label x , lookupBindName x] -- varName -- incl. label
   , try $ iden >>= lookupBindName -- holey names used as defined
   , TyListOf <$> brackets tt
   , parensExpr
   , P.List <$> brackets (tt `sepBy` reservedChar ',' <|> (scn $> []))
   ] <?> "ttArg"

  piBinder = reserved "Π" *> (many (iden >>= addArgName) >>= \pis -> addPiBound (PiBound pis WildCard))
  -- Catch potential implicit abstractions at each parens
  parensExpr = parens (choice [try piBound , (tt >>= \t -> tuple t <|> typedTT t) , scn $> Cons []]) >>= catchUnderscoreAbs
  tuple t = (\ts -> Cons (zip [-1,-2..] (t:ts))) <$> some (reservedChar ',' *> arg)
  label i = lookupSLabel i >>= \case
    Nothing -> P.Label <$ reserved "@" <*> newSLabel i <*> (many arg)
    Just l  -> pure $ P.Label l [] -- <$> many arg (converted in App)

  tySum = Gadt <$> let
    adtAlts = (,,Nothing) <$> (iden >>= newSLabel) <*> many appOrArg
    in some $ try (scn *> (reservedChar '|' *> lexeme adtAlts))

  tySumData = Gadt <$> do
    let labelDecl = (,,) <$> (iden >>= newSLabel) <*> many arg <*> optional tyAnn <?> "Label declaration"
    ref <- scn *> use indent <* svIndent
    indentedItems ref scn labelDecl (fail "")

  tyRecord = Cons <$> let fieldDecl = (,) <$> (iden >>= newFLabel) <*> tyAnn <?> "Field declaration" in do
    ref <- scn *> use indent <* svIndent
    indentedItems ref scn fieldDecl (fail "")

  con = let
    fieldAssign = (,) <$> (iden >>= newFLabel) <* reservedOp "=" <*> tt
    multilineAssign = do
      reserved "mkRecord"
      ref <- scn *> use indent <* svIndent
      indentedItems ref scn fieldAssign (fail "")
    conBraces = braces (fieldAssign `sepBy` reservedChar ',')
    in Cons <$> (multilineAssign <|> conBraces)

  doExpr = DoStmts <$> let
    doStmt = idenNo_ >>= \hNm -> choice
      [ reservedName "<-" *> addArgName hNm >>= \i -> tt <&> Bind i
      , lookupBindName hNm >>= \i -> tt <&> Sequence . \case
          App f ars -> App i (f : ars)
          expr      -> App i [expr]
      ]
    in do
    ref <- use indent <* scn
    L.indentLevel >>= \i -> case compare i ref of
      LT -> fail $ "new do statement is less indented than the reference indent: "
                   <> show i <> " < " <> show ref
      _  -> indentedItems ref scn doStmt (void (char ')'))

  caseSplits = let
    split = do
      svIndent
      lName <- idenNo_ >>= newSLabel
      ((pats , splitFn) , free) <- newArgNest $ do
        pats  <- many singlePattern
        reserved "=>"
        splitFn <- tt
        pure (pats , splitFn)
      pure (lName , free , pats , splitFn)
    splitIndent = do
      ref <- use indent <* scn
      L.indentLevel >>= \i -> case compare i ref of
        LT -> fail $ "new case statement is less indented than the reference indent: "
                     <> show i <> " < " <> show ref
        _  -> let finishEarly = void $ char ')' <|> lookAhead (reservedChar '_')
          in do  -- ')' and final match-all '_' can terminate indent
          alts     <- indentedItems ref scn split finishEarly
          catchAll <- optional $ reservedChar ' ' *> reserved "=>" *> tt
          pure (Match alts catchAll)
    splitBraces = fail "" --braces $ 
    in splitBraces <|> splitIndent
  match = do
    scrut  <- tt
    reserved "of"
    (`App` [scrut]) <$> caseSplits

  letIn = let
    pletBinds letStart (letRecT :: LetRecT) = newLetNest $ do
      scn -- go to first indented binding
      ref <- use indent
      svIndent -- tell linefold (and subsequent let-ins) not to eat our indentedItems
      indentedItems ref scn (funBind False letRecT) (reserved "in") <* reserved "in"
      tt
    in do
      letStart <- use indent
      inExpr <- (reserved "let" *> pletBinds letStart Let)
            <|> (reserved "rec" *> pletBinds letStart Rec)
      pure inExpr

  typedTT exp = optional tyAnn >>= \case --optional type annotation is parsed as anonymous let-binding
    Nothing -> pure exp
    Just WildCard  ->  pure exp -- don't bother if no info given (eg. pi binder)
    Just ty -> case exp of
      Var (VLocal l) -> addPiBound (PiBound [l] ty) *> pure exp
      x -> (Var . VBind <$> addAnonBindName)
        <* addBind (FnDef "typed-expr" LetOrRec Nothing 0 (FnMatch [] exp :| []) (Just ty))

  piBound = do
    i <- iden
    lookAhead (void (reservedChar ':') <|> reservedOp "::")
    (Var . VLocal <$> addArgName i) >>= typedTT

loneIden a i = lookupSLabel i <&> \case
  Nothing -> PArg a
  Just  l -> PComp a (PLabel l [])

-- TODO parse patterns as TT's to handle pi-bound arguments
pattern = let
  in choice
  [ try idenNo_ >>= \i -> choice -- addArgName i >>= \a -> choice
     [ some (singlePattern) >>= \args -> lookupSLabel i >>=
         maybe (newSLabel i) pure >>= \f -> addAnonArgName <&> \a -> PComp a (PLabel f args)
     , addNewArgName i >>= \a -> loneIden a i
     ]
  , singlePattern
  ]

-- Add anonymous arguments to prepare an extra Abs that accesses the patterns via lenses
singlePattern = let
  mkCompositePat cp = addAnonArgName <&> \a -> PComp a cp
  tuple p = (\tuplePats -> PTuple (p : tuplePats)) <$> some (reservedChar ',' *> pattern) >>= mkCompositePat
  in choice
  [ reservedChar '_' *> choice
    [ reservedName "as" *> lexeme idenNo_ >>= addNewArgName <&> PArg
    , addAnonArgName <&> \a -> PComp a PWildCard
    ]
  , try idenNo_ >>= \i -> addNewArgName i >>= \a -> loneIden a i

  -- Composites
  , let fieldPattern = lexeme idenNo_ >>= \iStr -> newFLabel iStr >>= \i -> (i,) <$> choice
          [ reservedName "as" *> pattern
          , PArg <$> addNewArgName iStr -- { A } pattern is same as { A=A }
          ]
    in (PCons <$> braces (fieldPattern `sepBy` reservedChar ',')) >>= mkCompositePat
  , (PLit <$> try literalP) >>= mkCompositePat
  , parens $ pattern >>= (\case
      PArg i -> option (PArg i) (PTyped i <$> tyAnn)
      p -> pure p
    ) >>= \p -> option p (tuple p)
  ] <?> "pattern"

---------------------
-- literal parsers --
---------------------
literalP = let
  signed p = let
    sign :: Bool -> Parser Bool =
      \i -> option i $ (single '+' *> sign i) <|> (single '-' *> sign (not i))
    in sign False >>= \s -> p <&> \n -> if s then negate n else n
  -- L.charLiteral handles escaped chars (eg. \n)
  char :: Parser Char = between (single '\'') (single '\'') L.charLiteral
  stringLiteral :: Parser [Char] = choice
    [ single '"'      *> manyTill L.charLiteral (single '"')
    , string "\"\"\"" *> manyTill L.charLiteral (string "\"\"\"") -- triple quotes """
    , string "''"     *> manyTill L.charLiteral (string "''")
    , string "$"      *> manyTill L.charLiteral endLine]
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
