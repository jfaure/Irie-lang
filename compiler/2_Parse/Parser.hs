{-# LANGUAGE OverloadedStrings , TemplateHaskell, RecursiveDo #-}
module Parser where

-- Parsing is responsible for converting all names to indexes into various vectors
--   1. VBind:   top-level let bindings
--   2. VLocal:  lambda-bound arguments (these don't index anything)
--   3. VExtern: out-ofscope HNames inamed now and resolved later
-- HNames are converted to INames on sight, and all issues of scope are resolved here
-- However: we cannot resolve infix trains yet (lack some fixities), and externs are opaque inames
--
-- Note: adding a bind must be done immediately after adding an IName
-- Use recursiveDo to guarantee this.

import Prim
import ParseSyntax as P

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad (void)
import Control.Applicative (liftA2)
import Data.Void
import Data.List (isInfixOf)
import qualified Data.Text as T
import qualified Data.Text.Read as TR
--import qualified Data.ByteString.Char8 as C -- so ghc realises char ~ Word8
import Control.Monad.State.Strict as ST
import Control.Monad.Reader
import Data.Functor
import Data.Foldable
import Data.Char (isAlphaNum , isDigit , isSpace)
import qualified Data.Vector as V
import qualified Data.Map as M
import qualified Data.Set as S
import GHC.Exts (groupWith)

import Control.Lens
import Control.Lens.Tuple
import Debug.Trace
import qualified Text.Megaparsec.Debug as DBG
dbg i = id
--dbg i = DBG.dbg i

data ParseState = ParseState {
   _indent    :: Pos  -- start of line indentation (need to save it for subparsers)
 , _moduleWIP :: Module
}
makeLenses ''ParseState

type Parser = ParsecT Void T.Text (ST.State ParseState)

---------------------------------------
-- INames and the vectors they index --
---------------------------------------
addBind b     = moduleWIP . bindings   %= (b:)
addImport i   = moduleWIP . imports    %= (i:)
addExtern e   = moduleWIP . externFns  %= (e:)

-- mixfixes are saved in lists based on first name
addMixFix m i = let
  p = moduleWIP . parseDetails
  in case m of -- drop the irrelevent parts of the MixFixDef
    MFName nm : m -> p . mixFixDefs %= M.insertWith (++) nm [(m , i)]
    MFHole : MFName nm : m -> p . postFixDefs %= M.insertWith (++) nm [(m , i)]

lookupMixFix m  = M.lookup m <$> use (moduleWIP . parseDetails . mixFixDefs)
lookupPostFix m = M.lookup m <$> use (moduleWIP . parseDetails . postFixDefs)

il = M.insertLookupWithKey (\k new old -> old)
-- Data.Map builtin size (good enough for labels/fields)
insertOrRetrieve h mp = let sz = M.size mp in case il h sz mp of 
  (Just x, mp) -> (x  , mp)
  (_,mp)       -> (sz , mp)
-- custom size variable (anonymous binds aren't in the map)
insertOrRetrieveSZ h (sz,mp) = case il h sz mp of 
  (Just x, mp) -> (x  , (sz,mp))
  (_,mp)       -> (sz , (sz+1,mp))
-- the list of args corresponds to a nest of function defs
-- if we're adding an argument, we do so to the first (innermost level)
insertOrRetrieveArg :: T.Text -> Int -> [M.Map T.Text Int] -> (Int, [M.Map T.Text Int])
insertOrRetrieveArg h sz argMaps = case argMaps of
  [] -> error "panic: empty function nesting" --impossible
  mp:xs -> case asum ((M.lookup h) <$> xs) of
    Just x        -> (x, argMaps)
    Nothing       -> case il h sz mp of 
      (Just x, _) -> (x  , argMaps)
      (_, mp')    -> (-1 , mp':xs)

pd = moduleWIP . parseDetails
addAnonArg = moduleWIP . parseDetails . nArgs <<%= (1+)
addArgName , addBindName , addUnknownName:: T.Text -> Parser IName
addArgName    h = do
  n <- use (moduleWIP . parseDetails . nArgs)
  s <- pd . hNameArgs     %%= insertOrRetrieveArg h n
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

lookupBindName h = use (moduleWIP . parseDetails) >>= \p -> let
  tryArg = VLocal <$> (asum $ (M.lookup h) `map` (p ^. hNameArgs))
  tryLet = VBind  <$> (asum $ (M.lookup h) `map` (p ^. hNameLocals))
  tryTop = VBind  <$> M.lookup h (p ^. hNameBinds . _2)
  in Var <$> case choice [tryArg , tryLet , tryTop] of
    Just i  -> pure i
    Nothing -> VExtern <$> addUnknownName h

-- function defs add a layer of lambda-bound arguments , same for let
incArgNest = moduleWIP . parseDetails . hNameArgs %= (M.empty :) -- increase arg nesting
decArgNest = moduleWIP . parseDetails . hNameArgs %= drop 1
incLetNest = moduleWIP . parseDetails . hNameLocals %= (M.empty :) -- increase arg nesting
decLetNest = moduleWIP . parseDetails . hNameLocals %= drop 1
newArgNest p = incArgNest *> p <* decArgNest 

lookupImplicit :: T.Text -> Parser IName -- implicit args
lookupImplicit h = do
  pd <- use $ moduleWIP . parseDetails
  case asum $ map (M.lookup h) (pd ^. hNameArgs) of
    Just arg -> pure $ arg
    Nothing  -> fail ("Not in scope: implicit arg '" ++ (T.unpack h) ++ "'")

-----------
-- Lexer --
-----------
-- A key convention: tokens consume trailing whitespace (use `symbol` or `lexeme`)
-- so parsers can assume they start on a non-blank.

--located :: Parser (Span -> a) -> Parser a = do
--  start <- getPosition
--  f <- p
--  end <- getPosition
--  pure $ f (Span (sourcePosToPos start) (sourcePosToPos end))

-- Space consumers: scn eats newlines, sc does not.
isSC x = isSpace x && x /= '\n'
sc :: Parser () = L.space (void $ takeWhile1P Nothing isSC) lineComment blockComment
scn :: Parser () = L.space space1 lineComment blockComment
lineComment = L.skipLineComment "--"
blockComment = L.skipBlockComment "{-" "-}"

lexeme, lexemen :: Parser a -> Parser a -- parser then whitespace
lexeme  = L.lexeme sc
lexemen = L.lexeme scn
symbol, symboln :: T.Text -> Parser T.Text --verbatim strings
symbol  = L.symbol sc
symboln = L.symbol scn

-- valid symbols in the language
-- all symbol chars = "!\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~"
--symbolChars = "!#$%&'*+,-/;<=>?@[]^|~" :: T.Text
reservedChars = "@.(){};_\\" -- TODO not ':' ?
--reservedOps   = T.words "= @ | : :: . ; => ( ) [ ] { }"
reservedNames = S.fromList $ T.words "if then else type data record class extern externVarArg let rec in where case of _ import require \\ : = ? | λ =>"
-- check the name isn't an iden which starts with a reservedWord
reservedName w = (void . lexeme . try) (string w *> notFollowedBy idenChars)
reservedChar c
  | T.any (==c) reservedChars = lexeme (char c)
  | otherwise = lexeme ((char c) <* notFollowedBy idenChars)
reservedOp = reservedName
reserved = reservedName

-----------
-- Names --
-----------
isIdenChar x = not (isSpace x) && not (T.any (==x) reservedChars)
idenChars = takeWhile1P Nothing isIdenChar
checkReserved x = if x `S.member` reservedNames
  then fail $ "keyword "++T.unpack x++" cannot be an identifier"
  else pure x
checkLiteral x = if isDigit `T.all` x -- TODO not good enough (1e3 , 2.0 etc..)
  then fail $ "literal: "++T.unpack x ++" cannot be an identifier"
  else pure x
checkIden = checkReserved <=< checkLiteral

-- We must use 'try', to backtrack if we parse a reserved word
iden :: Parser HName = lexeme . try $ (idenChars >>= checkIden)

-- separated and split on '_' (ie. argument holes)
mixFixDef :: Parser MixFixDef =
  some (choice [MFHole <$ char '_' , MFName <$> (checkIden =<< idenChars)]) >>= \case
    [MFHole] -> fail "'_' cannot be an identifier"
    mf -> pure mf

infixName = between (symbol "`") (symbol "`") iden

parens, braces, bracesn , brackets , bracketsn :: Parser a -> Parser a
parens  = between (symbol "(") (symbol ")")
braces  = between (symbol "{") (symbol "}")
bracesn = between (symboln "{") (symboln "}")
brackets  = between (symbol "[") (symbol "]")
bracketsn  = between (symboln "[") (symboln "]")
p `sepBy2` sep = (:) <$> p <*> (some (sep *> p))
endLine = lexeme (single '\n')

-- indentation shortcuts
noIndent = L.nonIndented scn . lexeme
iB = L.indentBlock scn
svIndent = L.indentLevel >>= (indent .=)

-- ref = reference indent level
-- lvl = lvl of first indented item (often == pos)
indentedItems ref lvl scn p finished = go where
 go = do
  scn
  pos <- L.indentLevel
  lookAhead (eof <|> finished) *> pure [] <|> if
     | pos <= ref -> pure []
     | pos == lvl -> (:) <$> p <*> go
     | otherwise  -> L.incorrectIndent EQ lvl pos

------------
-- Parser --
------------
parseModule :: FilePath -> T.Text
            -> Either (ParseErrorBundle T.Text Void) Module
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
     }

-- group declarations as they are parsed
doParse = void $ decl `sepEndBy` (endLine *> scn) :: Parser ()
decl = svIndent *> choice
   [ reserved "import" *> (iden >>= addImport)
   , extern
   , void funBind
   ]

extern =
 let _typed = reservedOp ":" *> tt
     doName = iden >>= \hNm -> addBindName hNm *> pure hNm
 in addExtern =<< choice
 [ Extern   <$ reserved "extern"      <*> doName <*> _typed
 , ExternVA <$ reserved "externVarArg"<*> doName <*> _typed
 ]

--infixDecl = let
--  pInfix = choice
--    [ reserved "infix"  $> AssocNone
--    , reserved "infixr" $> AssocRight
--    , reserved "infixl" $> AssocLeft]
--  opNames = (\x->[x]) <$> symbolName --`sepBy` symbol ","
--  in InfixDecl <$> pInfix <*> optional (lexeme L.decimal) <*> opNames

--pWhere :: Parser a -> Parser [a]
--pWhere pdecl = reserved "where" *> do
--  bracesn ((pdecl <* scn) `sepBy2` symboln ";") <|> do
--    ref <- use indent <* scn
--    lvl <- L.indentLevel
--    local (const lvl) $ indentedItems ref lvl scn pdecl (fail "_")

-------------------
-- Function defs --
-------------------
mixFix2Nm = T.concat . map (\case { MFName nm->nm ; MFHole->"_" })
funBind = lexeme mixFixDef >>= \case
  [MFName nm] -> funBind' nm (symbol nm *> many (lexeme pattern))
  mfDef -> let
    pMixFixArgs = \case
      []            -> pure []
      MFName nm : x -> symbol nm *> pMixFixArgs x
      MFHole   : x  -> (:) <$> lexeme pattern <*> pMixFixArgs x
    in mdo
    addMixFix mfDef i
    i <- funBind' (mixFix2Nm mfDef) (pMixFixArgs mfDef)
    pure i

funBind' :: T.Text -> Parser [Pattern] -> Parser TTName
funBind' nm pMFArgs = newArgNest $ mdo
  iNm <- addBindName nm -- handle recursive references
    <* addBind (FunBind nm implicits eqns ty) -- this should be done immediately (hence mdo)
  ars <- many pattern
  ann <- tyAnn
  let (implicits , ty) = case ann of { Just (i,t) -> (i,Just t) ; _ -> ([],Nothing) }
  eqns <- choice
    [ (:[]) <$> (FnMatch [] ars <$> (lexemen (reservedOp "=") *> tt))
    , case (ars , ann) of
        ([] , Just{})  -> some $ try (endLine *> fnMatch pMFArgs)
        (x  , Nothing) -> do fail $ "fn def lacks accompanying binding"
    ]
  pure (VBind iNm)

tyAnn :: Parser (Maybe ([IName] , TT)) = newArgNest $ do
  optional (reservedOp "::" *> bracesn ((iden >>= addArgName) `sepBy` reservedOp ";")) >>= \case
    Just implicits -> fmap (implicits,) <$> optional (reservedChar ':' *> tt)
    Nothing        -> fmap ([],)        <$> optional (reservedChar ':' *> tt)

-- TODO this duplicates some code in _funBind
lambda = reservedChar '\\'
  *> (Var . VBind <$> addAnonBindName) <* do 
    newArgNest $ mdo
      addBind $ FunBind "" [] eqns Nothing
      eqns <- (:[]) <$> ((fnArgs <* lexemen (reservedOp "=>")) <*> tt) -- fnMatch
      pure ()

--fnMatch pMFArgs = (fnArgs <* lexemen (reservedOp "=")) <*> tt
fnMatch pMFArgs = FnMatch [] <$> (pMFArgs <* lexemen (reservedOp "=")) <*> tt
fnArgs = let
  implicits = choice
   [ reservedOp "@" *> braces ((iden >>= lookupImplicit) `sepBy1` ";")
   , pure []
   ] in choice [ FnMatch <$> implicits <*> many (lexeme pattern) ]

-- We often need to parse a 2nd token to find out more about the first
-- eg. we have 2 'states' when parsing a tt
-- 1. `maybeApp` we may be parsing a fn app
-- 2. `arg` we are parsing arguments to an app (eg. Lit | parens app ..)
-- mixfix trains : parse out mixfixes assuming equal precedence , resolve that later
tt :: Parser TT = typedTT =<< choice
  [ letIn      -- "let"
  , multiIf    -- "if"
  , match      -- "case"
  , tySum      -- "|"
  , lambdaCase -- "\\case"
  , lambda     -- "\"
  , mixFixTrainOrArg
  ] <?> "tt"
  where
  postFix tt = (\(App f args) -> App f (tt:args)) <$> (iden >>= mixFix lookupPostFix)
  mixFixTrainOrArg = let
    tryPostFix fn = choice [postFix fn >>= tryPostFix , pure fn]
    in appOrArg >>= tryPostFix
  mixFix look i = look i >>= \case
    Nothing -> fail $ "not a mixFix namePart: " ++ T.unpack i
    Just mf -> choice (map doMixFix mf)
  doMixFix (mDef,i) = (App (Var i) <$>) . try $ pMixFix mDef
  pMixFix m = case m of -- generate a parser for a mixFixDef
    []            -> pure []
    MFName nm : x -> symbol nm *> pMixFix x
    MFHole    : x -> (:) <$> lexeme appOrArg  <*> pMixFix x
  mfIden = try $ iden >>= \i -> choice [
       mixFix lookupMixFix i
     , lookupPostFix i >>= \case
         Nothing -> choice [label i , lookupBindName i]
         Just x -> fail $ "reserved postfix iden: " ++ show i
     ]
  appOrArg = arg >>= \fn -> choice
    [ Proj fn <$ reservedChar '.' <*> (iden >>= newFLabel)
    , App fn <$> some arg
    , pure fn
    ]
  arg = choice
   [ WildCard <$ reserved "_"
   , con
   , mfIden
   , Lit <$> literalP
   , TyListOf <$> brackets tt
   , parens $ choice [try piBinder , (tt >>= typedTT)]
   ] <?> "arg tt"
  piBinder = do
    i <- lexeme iden
    lookAhead (void (reservedChar ':') <|> reservedOp "::")
    (Var . VLocal <$> addArgName i) >>= typedTT
  label i = P.Label <$ reservedOp "@" <*> newSLabel i <*> some arg

  tySum = let
    labeledTTs = do
      label <- iden >>= newSLabel
      tyAnn >>= \case
        Nothing -> fail "sum type annotation missing"
        Just (impls , ty) -> pure (label , impls , ty)
    in do TySum <$> some (try (scn *> (reservedChar '|' *> lexeme labeledTTs)))

  con = let
    fieldDecl = (,) <$> (iden >>= newFLabel) <* reservedOp "=" <*> arg
    in Cons <$> (braces $ fieldDecl `sepBy1` reservedOp ";")

  caseSplits = let
    split = (,,) <$> (iden >>= newSLabel) <* reservedOp "@"
      <*> pattern <* reservedOp "=>" <*> tt
    in Match <$> many (reservedOp "|" *> split)

  match = reserved "case" *> do
    scrut  <- tt
    (`App` [scrut]) <$> caseSplits
  lambdaCase = reserved "\\case" *> caseSplits

  multiIf = reserved "if" *> choice [try normalIf , multiIf]
    where
    normalIf = do
      ifThen <- (,) <$> tt <* reserved "then" <*> tt
      elseE  <- reserved "else" *> tt
      pure $ MultiIf [ifThen] elseE
    subIf = (,) <$ reservedOp "|" <*> tt <* reservedOp "=>" <*> tt

  letIn = reserved "let" *> do
    incLetNest
    ref <- use indent <* scn
    lvl <- L.indentLevel
    indentedItems ref lvl scn funBind (reserved "in")
    reserved "in"
    tt <* decLetNest

  typedTT exp = tyAnn >>= \case -- optional type annotation is parsed as anonymous let-binding
    Nothing -> pure exp
    Just ([] , WildCard)  ->  pure exp -- don't bother if no info given (eg. pi binder)
    Just (implicits , ty) -> (Var . VBind <$> addAnonBindName)
      <* addBind (FunBind "_:" [] [FnMatch [] [] exp] (Just ty))

pattern = singlePattern
singlePattern = dbg "pattern" $ choice
 [ PLit <$> literalP
 , PArg <$> (reserved "_" *> addAnonArg) -- wildcard pattern
 , PArg <$> (iden >>= addArgName)
 , parens typedPattern
 ]
typedPattern = singlePattern >>= \p -> choice
  [ PTyped p <$ reservedOp ":" <*> tt
  , pure p]

---------------------
-- literal parsers --
---------------------
literalP = let
  -- L.charLiteral handles escaped chars (eg. \n)
  char :: Parser Char = between (single '\'') (single '\'') L.charLiteral
  stringLiteral :: Parser String = choice
    [ single '\"'   *> manyTill L.charLiteral (single '\"')
    , (string "''") *> manyTill L.charLiteral (string "''")]
 in lexeme $ choice
   [ Char   <$> char
   , String <$> stringLiteral
   , Int    <$> L.decimal
   , numP
   ]

decimal_ , dotDecimal_ , exponent_ :: Parser T.Text
decimal_    = takeWhile1P (Just "digit") isDigit
dotDecimal_ = char '.' *> takeWhile1P (Just "digit") isDigit
exponent_   = char' 'e' *> decimal_

numP :: Parser Literal = --T.Text =
  let unJ = \case { Just x->x ; _ -> T.empty }
  in do
  c <- decimal_
  f <- optional dotDecimal_
  e <- optional exponent_
  pure $ case (f , e) of
    (Nothing , Nothing) -> PolyInt c
    _ -> PolyFrac $ c `T.snoc` '.' `T.append` unJ f `T.append` unJ e
