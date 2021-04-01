{-# LANGUAGE TemplateHaskell #-}
module Parser (parseModule , parseMixFixDef) where

-- Parsing is responsible for converting all names to indexes into various vectors
--   1. VBind:   top-level let bindings
--   2. VLocal:  lambda-bound arguments
--   3. VExtern: out-ofscope HNames inamed now and resolved later
-- * HNames are converted to INames on sight
-- * name scoped is checked and freeVars are noted
-- However: we cannot resolve externs (so make opaque inames) or infix trains yet (lacking some fixities)
--
-- Note: adding a bind must be done immediately after adding an IName to enforce consistency
-- recursiveDo solves this trivially

import Prim
import ParseSyntax as P

import Text.Megaparsec-- hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Data.Text as T
import Control.Monad (fail)
--import qualified Data.Vector as V
import qualified Data.Map as M
import qualified Data.IntSet as IS
import qualified Data.Set as S
import Control.Lens

--import qualified Text.Megaparsec.Debug as DBG
dbg i = identity -- DBG.dbg i

data ParseState = ParseState {
   _indent          :: Pos         -- start of line indentation (need to save it for subparsers)
 , _parsingMixFixes :: [MixFixDef] -- we're parsing a mixfix: these are the options
 , _piBound         :: [[ImplicitArg]]
 , _moduleWIP       :: Module
 , _tmpReserved     :: [S.Set Text]
}
makeLenses ''ParseState

--type Parser = ParsecT Void Text (ST.State ParseState)
type Parser = ParsecT Void Text (Prelude.State ParseState)

--getOffset

--------------------
-- Lens machinery --
--------------------
addBind b     = moduleWIP . bindings   %= (b:)
addImport i   = moduleWIP . imports    %= (i:)
addExtern e   = moduleWIP . externFns  %= (e:)
addPiBound  p = piBound %= \(x:xs)->(p:x):xs
getPiBounds f = do
  piBound %= ([]:)
  r <- f
  pis <- fromJust . head <$> (piBound <<%= drop 1)
  pure (pis , r)

-- mixfixes are saved in lists based on first name
addMixFix m i = let
  p = moduleWIP . parseDetails
  in case m of -- drop the irrelevent parts of the MixFixDef
    MFName nm : m -> p . mixFixDefs %= M.insertWith (++) nm [(m , i)]
    MFHole : MFName nm : m -> p . postFixDefs %= M.insertWith (++) nm [(m , i)]

lookupMixFix m  = M.lookup m <$> use (moduleWIP . parseDetails . mixFixDefs)
lookupPostFix m = M.lookup m <$> use (moduleWIP . parseDetails . postFixDefs)

il = M.insertLookupWithKey (\k new old -> old)
-- Data.Map's builtin size is good enough for labels/fields
insertOrRetrieve h mp = let sz = M.size mp in case il h sz mp of 
  (Just x, mp) -> (x  , mp)
  (_,mp)       -> (sz , mp)
-- custom size variable (anonymous binds aren't named in the map)
insertOrRetrieveSZ h (sz,mp) = case il h sz mp of 
  (Just x, mp) -> (x  , (sz,mp))
  (_,mp)       -> (sz , (sz+1,mp))
-- the list of args corresponds to a nest of function defs
-- if we're adding an argument, we do so to the first (innermost level)
insertOrRetrieveArg :: Text -> Int -> [M.Map Text Int] -> (Int, [M.Map Text Int])
insertOrRetrieveArg h sz argMaps = case argMaps of
  [] -> error "panic: empty function nesting" --impossible
  mp:xs -> case asum (M.lookup h <$> xs) of
    Just x        -> (x, argMaps)
    Nothing       -> case il h sz mp of 
      (Just x, _) -> (x  , argMaps)
      (_, mp')    -> (-1 , mp':xs)

pd = moduleWIP . parseDetails
addAnonArg = moduleWIP . parseDetails . nArgs <<%= (1+)
addArgName , addBindName , addUnknownName:: Text -> Parser IName
addArgName    h = do
  n <- use (moduleWIP . parseDetails . nArgs)
  s <- pd . hNameArgs %%= insertOrRetrieveArg h n
  if s < 0 then (moduleWIP . parseDetails . nArgs <<%= (1+)) else pure s

-- search (local let bindings) first, then the main bindMap
addBindName   h = do
  n <- use (moduleWIP . parseDetails . hNameBinds . _1)
  use (moduleWIP . parseDetails . hNameLocals) >>= \case
    [] -> pd . hNameBinds  %%= insertOrRetrieveSZ h
    _  -> pd . hNameLocals %%= insertOrRetrieveArg h n

addAnonBindName = (moduleWIP . parseDetails . hNameBinds . _1 <<%= (+1))
addUnknownName h = pd . hNamesNoScope %%= insertOrRetrieve h

newFLabel h = moduleWIP . parseDetails . fields %%= insertOrRetrieve h
newSLabel h = moduleWIP . parseDetails . labels %%= insertOrRetrieve h
lookupSLabel h = M.lookup h <$> use (moduleWIP . parseDetails . labels)

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
  case asum $ map (M.lookup h) (pd ^. hNameArgs) of
    Just arg -> pure $ arg
    Nothing  -> fail ("Not in scope: implicit arg '" ++ (T.unpack h) ++ "'")

-----------
-- Lexer --
-----------
-- A key convention: tokens consume trailing whitespace (using `symbol` or `lexeme`)
-- so parsers can assume they start on a non-blank.

--located :: Parser (Span -> a) -> Parser a = do
--  start <- getPosition
--  f <- p
--  end <- getPosition
--  pure $ f (Span (sourcePosToPos start) (sourcePosToPos end))

-- Space consumers: scn eats newlines, sc does not.
isSC x = isSpace x && x /= '\n'
sc  :: Parser () = L.space (void $ takeWhile1P Nothing isSC) lineComment blockComment
scn :: Parser () = L.space space1 lineComment blockComment
endLine = lexeme (single '\n')
lineComment = L.skipLineComment "--"
blockComment = L.skipBlockComment "{-" "-}"

lexeme, lexemen :: Parser a -> Parser a -- parser then whitespace
[lexeme, lexemen]   = L.lexeme <$> [sc , scn]
symbol, symboln :: Text -> Parser Text --verbatim strings
[symbol , symboln]  = L.symbol <$> [sc , scn]

parens, braces, bracesn , brackets , bracketsn :: Parser a -> Parser a
parens    = (symbol  "(") `between` (symbol  ")")
braces    = (symbol  "{") `between` (symbol  "}")
bracesn   = (symboln "{") `between` (symboln "}")
brackets  = (symbol  "[") `between` (symbol  "]")
bracketsn = (symboln "[") `between` (symboln "]")
p `sepBy2` sep = (:) <$> p <*> (some (sep *> p))

-----------
-- Names --
-----------
--symbolChars = "!#$%&'*+,-/;<=>?@[]^|~" :: Text
reservedChars = "'@(){};,\\\""
reservedNames = S.fromList $ words "set over . if then else type data record class extern externVarArg let rec in where case of _ import require \\ : :: = ? | λ =>"
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
  then fail $ "keyword " <> toS x <> " cannot be an identifier"
  else pure x
checkLiteral x = if isDigit `T.all` x -- TODO not good enough (1e3 , 2.0 etc..)
  then fail $ "literal: " <> toS x <> " cannot be an identifier"
  else pure x
checkIden = checkReserved <=< checkLiteral

-- We must use 'try', to backtrack if we parse a reserved word
iden :: Parser HName = lexeme . try $ (idenChars >>= checkIden)
idenNo_ = lexeme idenNo_'
idenNo_' = try $ (takeWhile1P Nothing (\x->isIdenChar x && x /= '_') >>= checkIden)

-- separated and split on '_' (ie. argument holes)
mixFixDef :: Parser MixFixDef = lexeme $ do
  some (choice [MFHole <$ char '_' , MFName <$> idenNo_']) >>= \case
    [MFHole] -> fail "'_' cannot be an identifier"
    mf -> pure mf
-- exported convenience function for use by builtins (Externs.hs)
parseMixFixDef :: Text -> Either (ParseErrorBundle Text Void) [MixFixName]
 = \t -> runParserT mixFixDef "<internal>" t `evalState` _

-- ref = reference indent level
-- lvl = lvl of first indented item (often == pos)
indentedItems prev scn p finished = L.indentLevel >>= go where
 go lvl = scn *> do
  pos <- L.indentLevel
  [] <$ lookAhead (eof <|> finished) <|> if
     | pos <= prev -> pure []
     | pos == lvl  -> (:) <$> p <*> go lvl
     | otherwise   -> L.incorrectIndent EQ lvl pos
svIndent = L.indentLevel >>= (indent .=)

------------
-- Parser --
------------
parseModule :: FilePath -> Text
            -> Either (ParseErrorBundle Text Void) Module
  = \nm txt ->
  let startModule = Module {
          _moduleName = T.pack nm
        , _imports = []
        , _externFns = []
        , _bindings= []
        , _parseDetails = ParseDetails {
             _mixFixDefs    = M.empty
           , _postFixDefs   = M.fromList [("->" , [([MFHole] , VExtern 0)])]
           , _hNameBinds    = (0 , M.empty)
           , _hNameArgs     = [] -- stack of lambda-bounds
           , _hNameLocals   = []
           , _freeVars      = IS.empty
           , _nArgs         = 0
           , _hNamesNoScope = M.fromList [("->",0)]-- M.empty
           , _fields        = M.empty
           , _labels        = M.empty
        }
      }
      end = (bindings %~ reverse)
  in end <$> runParserT (scn *> doParse *> eof *> use moduleWIP) nm txt
  `evalState` ParseState {
       _indent     = mkPos 1
     , _moduleWIP  = startModule
     , _parsingMixFixes = []
     , _tmpReserved = []
     , _piBound = []
     }

-- group declarations as they are parsed
doParse = void $ decl `sepEndBy` (endLine *> scn) :: Parser ()
decl = svIndent *> choice
   [ reserved "import" *> (iden >>= addImport)
   , extern
   , void funBind <?> "binding"
   , bareTT
   ]

-- for the repl
bareTT = addAnonBindName *> ((\tt -> addBind (FunBind "replExpr" [] IS.empty [FnMatch [] [] tt] Nothing)) =<< tt)

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
mixFix2Nm = T.concat . map (\case { MFName nm->nm ; MFHole->"_" })
funBind = lexeme mixFixDef >>= \case
  [MFName nm] -> funBind' nm (symbol nm *> many (lexeme singlePattern))
  mfDef -> let
    pMixFixArgs = \case
      []            -> pure []
      MFName nm : x -> symbol nm *> pMixFixArgs x
      MFHole    : x -> (:) <$> lexeme singlePattern <*> pMixFixArgs x
    in mdo
    addMixFix mfDef i
    i <- funBind' (mixFix2Nm mfDef) (pMixFixArgs mfDef)
    pure i

funBind' :: Text -> Parser [Pattern] -> Parser TTName
funBind' nm pMFArgs = newArgNest $ mdo
  iNm <- addBindName nm -- handle recursive references
    <* addBind (FunBind nm (implicits ++ pi) free eqns ty)
  ars <- many singlePattern
  ann <- tyAnn
  let (implicits , ty) = case ann of { Just (i,t) -> (i,Just t) ; _ -> ([],Nothing) }
  (pi , eqns) <- getPiBounds $ choice
    [ (:[]) <$> fnMatch (pure ars) (reserved "=") -- (FnMatch [] ars <$> (lexemen (reservedOp "=") *> tt))
    , case (ars , ann) of
        ([] , Just{})  -> some $ try (endLine *> fnMatch pMFArgs (reserved "=") )
        (x  , Just{})  -> fail "TODO no parser for: fn args followed by type sig"
        (x  , Nothing) -> do fail $ "fn def lacks accompanying binding"
    ]
  free <- getFreeVars
  pure (VBind iNm)

tyAnn :: Parser (Maybe ([ImplicitArg] , TT)) = let
    implicitArg = (,) <$> (iden >>= addArgName) <*> optional (reservedChar ':' *> tt)
  in newArgNest $ do
  optional (reserved "::" *> bracesn (implicitArg `sepBy` reserved ";")) >>= \case
    Just implicits -> fmap (implicits,) <$> optional (reservedChar ':' *> tt)
    Nothing        -> fmap ([],)        <$> optional (reservedChar ':' *> tt)

--lambda = reservedChar '\\' *> (Var . VBind <$> addAnonBindName) <* do 
--  newArgNest $ mdo
--    addBind $ FunBind "_" [] free eqns Nothing
--    eqns <- (:[]) <$> fnMatch (many singlePattern) (reserved "=>")
--    free <- getFreeVars
--    pure ()
lambda = reservedChar '\\' *> do
  newArgNest $ do
    eqns <- (:[]) <$> fnMatch (many singlePattern) (reserved "=>")
    free <- getFreeVars
    pure $ Abs $ FunBind "lambda" [] free eqns Nothing

fnMatch pMFArgs sep = -- sep is "=" or "=>"
  -- TODO is hoistLambda ideal here ?
  let hoistLambda = try $ lexemen sep *> reservedChar '\\' *> notFollowedBy (string "case") *> newArgNest (fnMatch (many singlePattern) (reserved "=>"))
      normalFnMatch = FnMatch [] <$> (pMFArgs <* lexemen sep) <*> tt
  in choice [ hoistLambda , normalFnMatch ]

--fnArgs = let
--  implicits = option [] $ reservedOp "@" *> braces ((iden >>= lookupImplicit) `sepBy1` ";")
--  in FnMatch <$> implicits <*> many (lexeme pattern)

-- TT parser
-- We often need to parse a 2nd token to find out more about the first
-- eg. after an arg, if there is another arg, the first arg is a fn app
-- mixfix trains : parse out mixfixes assuming equal precedence , we deal with that later
data MFLArg = MFLArgTT TT | MFLArgNone | MFLArgHole
ttArg , tt :: Parser TT
(ttArg , tt) = (arg , anyTT)
  where
  anyTT = typedTT =<< choice
    [ letIn      -- "let"
    , match      -- "case"
    , tySum      -- "|"
    , mixFixTrainOrArg
--  , appOrArg
    ] <?> "tt"
--appOrArg = mfApp <|> arg >>= \fn -> option fn $ choice
  appOrArg = arg >>= \fn -> option fn (choice
    [ -- Proj fn <$ reservedChar '.' <*> (idenNo_ >>= newFLabel)
--  , lexeme (char ',') *> ((\t -> P.Label 0 [t]) <$> appOrArg)
      case fn of
--      Lit l -> LitArray . (l:) <$> some literalP
        P.Label l [] -> P.Label l <$> some arg
        fn -> App fn <$> some arg
    ]) >>= \tt -> option tt (lens tt)
--lens target = let checkOK = \case { TTLens _ [] Nothing -> fail "empty lens" ; x -> pure x }
--  in many (try $ reservedChar '.' *> (idenNo_ >>= newFLabel)) >>=
--    \path -> (TTLens target path <$> optional (reservedChar '.' *> reserved "set" *> arg)) >>= checkOK
  lens :: TT -> Parser TT
  lens record = let
    lensNext path = reservedChar '.' *> choice [
        TTLens record (reverse path) <$> (LensSet  <$ reserved "set"  <*> arg)
      , TTLens record (reverse path) <$> (LensOver <$ reserved "over" <*> arg)
      , idenNo_ >>= newFLabel >>= \p -> choice [lensNext (p : path) , pure (TTLens record (reverse (p:path)) LensGet)]
      ]
    in lensNext []
  arg = choice
   [ reserved "_" $> WildCard
   , lambdaCase -- "\\case"
   , lambda     -- "\"
   , con
   , try $ idenNo_ >>= varName -- incl. label
   , Lit <$> literalP
-- , some literalP <&> \case { [l] -> Lit l ; ls -> LitArray ls }
   , TyListOf <$> brackets tt
   , parens $ choice [try piBinder , (tt >>= typedTT) , scn $> Cons []]
   , P.List <$> brackets (tt `sepBy` reservedChar ',' <|> (scn $> []))
   ] <?> "ttArg"
  label i = lookupSLabel i >>= \case
    Nothing -> P.Label <$ reservedOp "@" <*> newSLabel i <*> (many arg)
    Just l  -> pure $ P.Label l [] -- <$> many arg (converted in App)

  tySum = TySum <$> let
    labeledTTs = do
      label <- iden >>= newSLabel
      getPiBounds tyAnn >>= \case
        (pis , Nothing) -> fail "sum type annotation missing"
        (pis , Just (impls , ty)) -> pure (label , pis ++ impls , ty)
    in some $ try (scn *> (reservedChar '|' *> lexeme labeledTTs))

  con = let
    fieldAssign = (,) <$> (iden >>= newFLabel) <* reservedOp "=" <*> tt
    conHash = let
  --  in braces $ fieldDecl `sepBy1` reservedChar ';'
      in do
      string "##"
      ref <- use indent <* scn
      indentedItems ref scn fieldAssign (fail "")
    conBraces = braces (fieldAssign `sepBy` reservedChar ',')
    in Cons <$> (conHash <|> conBraces)

  caseSplits = Match <$> let
    split = newArgNest $ mdo
      lName <- iden >>= newSLabel
      optional (reservedChar '@')
      pats <- many singlePattern
      reserved "=>"
      splitFn <- tt
      free <- getFreeVars
      pure (lName , free , pats , splitFn)
    in choice [some $ try (scn *> reservedChar '|' *> split) , pure <$> split]
  match = reserved "case" *> do
    scrut  <- tt
    reserved "of"
    (`App` [scrut]) <$> caseSplits

  lambdaCase = reserved "\\case" *> caseSplits

  letIn = reserved "let" *> do
    incLetNest
    ref <- use indent <* scn
    indentedItems ref scn funBind (reserved "in") <* reserved "in"
    tt <* decLetNest

  typedTT exp = tyAnn >>= \case -- optional type annotation is parsed as anonymous let-binding
    Nothing -> pure exp
    Just ([] , WildCard)  ->  pure exp -- don't bother if no info given (eg. pi binder)
    Just (implicits , ty) -> case exp of
      Var (VLocal l) -> addPiBound (l , Just ty) *> pure exp
      x -> (Var . VBind <$> addAnonBindName)
        <* addBind (FunBind "_:" [] IS.empty [FnMatch [] [] exp] (Just ty))

  piBinder = do
    i <- iden
    lookAhead (void (reservedChar ':') <|> reservedOp "::")
    (Var . VLocal <$> addArgName i) >>= typedTT

  --------------
  -- MixFixes --
  --------------
  postFix tt = mixFixDef >>= \md -> case md of
    MFName h : xs -> mixFix md (MFLArgTT tt) lookupPostFix h
    x -> fail "expected postfix (mixfix)"
  mixFixTrainOrArg = let tryPostFix fn = option fn (postFix fn >>= tryPostFix)
    in appOrArg >>= tryPostFix
  mixFix parsedDef lArg look i = let
    doMixFix parsedDef lArg ms = do
      let mkBody i args = App (Var i) $ case lArg of { MFLArgTT i->(i:args) ; _->args }
      lambdaBound <- case lArg of { MFLArgHole->addAnonArg <&> (\x->[x]) ; _ -> pure [] }
      try (pLMF parsedDef (ms , lambdaBound)) >>= \case
        (i , args , []) -> pure $ mkBody i args
        (i , args , lambdaBound) -> (Var . VBind <$> addAnonBindName) <*
          (let fnMatche = FnMatch [] (PArg <$> lambdaBound) (mkBody i args)
          in  addBind $ FunBind "λMF" [] IS.empty [fnMatche] Nothing
          )
    -- Lambda MixFixes are a slight complication ; we must spawn an anonymous function for them
    -- and collect potential (implicitly bound) lambda-bound arguments
    pLMF :: MixFixDef -> ([(MixFixDef,TTName)] , [IName]) -> Parser (TTName , [TT] , [IName])
    pLMF parsedMF (possibleMFs , lBound) = do
      let stripPrefix [] (ys,i) = Just (ys,i)
          stripPrefix (x:xs) ((y:ys),i) | x == y = stripPrefix xs (ys,i)
          stripPrefix _ _ = Nothing
      lBounds  <- (length $ filter (==MFHole) parsedMF) `replicateM` addAnonArg
      let lamArgs = Var . VLocal <$> lBounds -- non-null if lambda-mixfix
          matches = catMaybes $ stripPrefix parsedMF <$> possibleMFs
      case snd <$> filter (null . fst) matches of
        x:xs:_-> fail "amibuous mixfix parse"
        [i]   -> pure (i , lamArgs , lBounds ++ lBound)
        []    -> case matches of
          [([MFHole] , i)] -> (\x->(i , x:lamArgs , lBounds ++ lBound)) <$> lexeme appOrArg
          x -> let
            next = let startsWithHole = \case {(MFHole:xs,_)->True ; _->False}
              in (\(a,b)->(drop 1 a,b)) <$> filter startsWithHole matches
            tmpReserved = let getNm = (\case { MFName nm:_->nm ; x->error "unexpected mf hole" })
              in S.fromList $ getNm . fst <$> next
            merge = \x (i,a,b)->(i , x:a++lamArgs , lBound++b)
            in merge <$> withTmpReserved tmpReserved appOrArg
                     <*> (mixFixDef >>= (`pLMF` (next , lBounds)))
    in look i >>= \case
      Nothing -> fail $ "not a mixFix namePart: " ++ T.unpack i
      Just mf -> doMixFix parsedDef lArg $ (\(a,b)->(MFName i:a,b)) <$> mf
  mfApp = try mixFixDef >>= \md -> case md of
    MFHole : MFName h : x -> mixFix (MFName h : x) MFLArgNone lookupPostFix h
    MFName i : x -> choice [ mixFix md MFLArgNone lookupMixFix i , varName i ]
  -- fail if varName is a mixfix name-part
  varName nm = ((\case {[]->False ; (s:_)->S.member nm s}) <$> use tmpReserved) >>= \case
    True  -> fail $ "temporarily reserved mixfix name-part: " ++ show nm
    False -> lookupPostFix nm >>= \case
      Nothing -> choice [label nm , lookupBindName nm]
      Just x  -> fail $ "reserved postfix iden: " ++ show nm

--pattern = choice [ try single , PTT <$> ttArg ] <?> "pattern"
-- Need to parse patterns as TT's to handle pi-bound arguments
pattern = choice
 [ try (singlePattern >>= \x -> option x (PApp x <$> some singlePattern))
 , PTT <$> ttArg]
singlePattern = choice
 [ iden >>= \i -> lookupSLabel i >>= \case
     Nothing -> PArg <$> addArgName i
     Just  x -> PApp (PArg x) <$> many singlePattern
 , parens pattern
 ]
--piBound h = do
--  tyAnn <- reservedChar ':' *> tt
--  i <- addArgName h
--  addPiBound (i , tyAnn)
--  pure $ PTyped (PArg i) tyAnn
--pattern = singlePattern -- >>= \x -> option x (PApp x <$> parens (some singlePattern))
--singlePattern = choice
-- [ PLit <$> literalP
-- , PArg <$> (reserved "_" *> addAnonArg) -- wildcard pattern
---- , iden >>= \i -> lookupSLabel i >>= \case
----     Nothing -> addArgName i
----     Just  x -> PApp <$> many singlePattern
-- , iden >>= \h -> choice
--    [ piBound h
--    , PArg <$> addArgName h
--    ]
-- , parens singlePattern
-- ]
--typedPattern = let
--  in singlePattern >>= \p -> option p piBound

---------------------
-- literal parsers --
---------------------
literalP = let
  -- L.charLiteral handles escaped chars (eg. \n)
  char :: Parser Char = between (single '\'') (single '\'') L.charLiteral
  stringLiteral :: Parser [Char] = choice
    [ single '\"'   *> manyTill L.charLiteral (single '\"')
    , (string "\"\"\"") *> manyTill L.charLiteral (string "\"\"\"")
    , (string "''") *> manyTill L.charLiteral (string "''")
    , (string "$") *> manyTill L.charLiteral endLine]
  intLiteral = choice
    [ L.decimal
    , string "0b" *> L.binary
    , string "0x" *> L.hexadecimal
    , string "0o" *> L.octal
    ]
 in lexeme $ choice
   [ Char   <$> char
   , String <$> stringLiteral
   , Int    <$> intLiteral
   , numP
   ]

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
