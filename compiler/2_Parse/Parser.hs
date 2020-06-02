{-# LANGUAGE OverloadedStrings , TemplateHaskell #-}
{-# LANGUAGE LambdaCase, ScopedTypeVariables , MultiWayIf , StandaloneDeriving , RecursiveDo #-}
module Parser where

-- Parsing is responsible for:
-- * converting all names to indexes into various vectors
--   1. VBind:   top-level let bindings
--   2. VLocal:  lambda-bound arguments (these don't index anything)
--   3. VExtern: out-ofscope variables to be resolved later
-- * Lifting all let-bindings (incl resolving free-vars)
-- * figuring out (relative) universes from context
-- * identifying functions that return terms

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
import Data.Char (isAlphaNum , isDigit)
import qualified Data.Vector as V
--import qualified Data.HashMap.Strict as HM
import qualified Data.Map as M
import GHC.Exts (groupWith)

import Control.Lens
import Control.Lens.Tuple
import Debug.Trace
import qualified Text.Megaparsec.Debug as DBG
dbg i = id
--dbg i = DBG.dbg i

data ParseState = ParseState {
   _indent   :: Pos  -- start of line indentation (need to save it for subparsers)
 , _nBinds   :: Int
-- , _nImports :: Int
 , _moduleWIP  :: Module
}
makeLenses ''ParseState

type Parser = ParsecT Void T.Text (ST.State ParseState)

---------------------------
-- Convenience functions --
---------------------------
newIndent new = indent .= new
addBind b     = moduleWIP . bindings %= (b:)
addImport i   = moduleWIP . imports  %= (i:)

il = M.insertLookupWithKey (\k new old -> old)

-- use Data.Map builtin size
insertOrRetrieve h mp = let sz = M.size mp in case il h sz mp of 
  (Just x, mp) -> (x  , mp)
  (_,mp)       -> (sz , mp)

-- use custom size variable - since some binds are anonymous
insertOrRetrieveSZ h (sz,mp) = case il h sz mp of 
  (Just x, mp) -> (x  , (sz,mp))
  (_,mp)       -> (sz , (sz+1,mp))

-- the list of args corresponds to a nest of function defs
-- if we're adding an argument, we do so to the first (innermost level)
insertOrRetrieveArg h sz argMaps = case argMaps of
  [] -> error "panic: empty function nesting" --impossible
  mp:xs -> case asum ((M.lookup h) <$> xs) of
    Just x        -> (x, argMaps)
    Nothing       -> case il h sz mp of 
      (Just x, _) -> (x  , argMaps)
      (_, mp')    -> (-1 , mp':xs)

pd = moduleWIP . parseDetails
addArgName , addBindName , addImportName:: T.Text -> Parser IName
addArgName    h = do
  n <- use (moduleWIP . parseDetails . nArgs)
  s <- pd . hNameArgs     %%= insertOrRetrieveArg h n
  if s < 0 then (moduleWIP . parseDetails . nArgs %= (1+)) *> pure n else pure s
addBindName   h = pd . hNameBinds    %%= insertOrRetrieveSZ h
addAnonBindName = (moduleWIP . parseDetails . hNameBinds . _1 <<%= (+1))
addImportName h = pd . hNamesNoScope %%= insertOrRetrieve h

newFLabel h = moduleWIP . parseDetails . fields %%= insertOrRetrieve h
newSLabel h = moduleWIP . parseDetails . labels %%= insertOrRetrieve h

-- try first the argmap, then the bindmap, else assume the name is imported
lookupBindName h = do
  pd <- use $ moduleWIP . parseDetails
  Var <$> case asum $ map (M.lookup h) (pd ^. hNameArgs) of
    Just arg  -> pure $ VLocal arg
    Nothing   -> case M.lookup h (pd ^. hNameBinds . _2) of
      Just bind -> pure $ VBind bind
      Nothing   -> VExtern <$> addImportName h

-- each new function definition adds a layer of lambda-bound arguments
incArgNest = moduleWIP . parseDetails . hNameArgs %= (M.empty :) -- increase arg nesting
clearLocals = moduleWIP . parseDetails . hNameArgs %= drop 1

lookupImplicit :: T.Text -> Parser IName
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
lineComment = L.skipLineComment "--"
blockComment = L.skipBlockComment "{-" "-}"
scn :: Parser () -- space and newlines
  = L.space space1 lineComment blockComment
sc :: Parser () -- space
  = L.space (void $ takeWhile1P Nothing f) lineComment blockComment
   where f x = x == ' ' || x == '\t'

lexeme, lexemen :: Parser a -> Parser a -- parser then whitespace
lexeme  = L.lexeme sc
lexemen = L.lexeme scn
symbol, symboln :: String -> Parser T.Text --verbatim strings
symbol  = L.symbol sc . T.pack
symboln = L.symbol scn . T.pack

-- valid symbols in the language
-- all symbol chars = "!\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~"
-- reserved: ():\{}"_'`.
symbolChars = "!#$%&'*+,-/;<=>?@[]^|~" :: T.Text
reservedOps   = T.words "= @ | : :: . ; => ( ) [ ] { }"
reservedNames = T.words "if then else type data record class extern externVarArg let rec in where case of _ import require"
reservedName w = (lexeme . try) (string (T.pack w) *> notFollowedBy alphaNumChar)
reservedOp w = lexeme (notFollowedBy (opLetter w) *> string w)
  where opLetter :: T.Text -> Parser ()
        opLetter w = void $ choice (string <$> longerOps w)
        longerOps w = filter (\x -> T.isInfixOf w x && x /= w) reservedOps
reserved = reservedName

-----------
-- Names --
-----------
-- We must use try to backtrack if we parse a reserved word
iden :: Parser HName = try $ lexeme (p >>= check) where
  p :: Parser T.Text
  p = lookAhead letterChar *> takeWhileP Nothing isAlphaNum
  check x = if x `elem` reservedNames
    then fail $ "keyword "++show x++" cannot be an identifier"
    else pure x
_lIden, _uIden :: Parser HName
_lIden = lookAhead lowerChar *> iden
_uIden = lookAhead upperChar *> iden
pIden    = iden   >>= lookupBindName
newLIden = _lIden >>= addBindName
newUIden = _uIden >>= addBindName

_symbolName = try $ lexeme (p >>= check) where
  p :: Parser T.Text
  p = takeWhile1P Nothing ((`T.any` symbolChars) . (==))
  check x = if x `elem` reservedOps
    then fail $ "reserved Symbol: "++show x ++" cannot be an identifier"
    else pure  x
symbolName :: Parser TT = lookupBindName =<< _symbolName

infixName = between (symbol "`") (symbol "`") pIden <|> symbolName
qualifier = pIden -- not a symbol
-- TODO add to importNames
qName :: Parser IName -> Parser IName
qName p = lexeme $ many (try (qualifier <* reservedOp "."))
  >>= \case
  []  -> p
  nms -> p

-- literals
int    :: Parser Integer = lexeme L.decimal
double :: Parser Double  = lexeme L.float
-- L.charLiteral handles escaped chars (eg. \n)
charLiteral :: Parser Char = between (single '\'') (single '\'') L.charLiteral
stringLiteral :: Parser String = choice
  [ single '\"'   *> manyTill L.charLiteral (single '\"')
  , (string "''") *> manyTill L.charLiteral (string "''")]

parens, braces, bracesn :: Parser a -> Parser a
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
svIndent f = L.indentLevel >>= newIndent

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

--debug functions
dbgToEof = traceShowM =<< (getInput :: Parser T.Text)
d = dbgToEof
db x = traceShowM x *> traceM ": " *> d

------------
-- Parser --
------------
parseModule :: FilePath -> T.Text
            -> Either (ParseErrorBundle T.Text Void) Module
  = \nm txt ->
  let startModule = Module {
          _moduleName = T.pack nm
        , _imports = []
        , _bindings= []
        , _parseDetails = ParseDetails {
             _hNameBinds    = (0 , M.empty) -- init at -1 so (ret (1+) lines up with indexes)
           , _hNameArgs     = [] -- stack of lambda-bounds
           , _nArgs         = 0
           , _hNamesNoScope = M.empty
           , _fields        = M.empty
           , _labels        = M.empty
        }
      }
      end = (bindings %~ reverse)
  in end <$> runParserT (scn *> doParse *> eof *> use moduleWIP) nm txt
  `evalState` ParseState {
       _indent = mkPos 1
     , _nBinds   = 0
     , _moduleWIP  = startModule
     }

-- group declarations as they are parsed
doParse = void $ decl `sepEndBy` (endLine *> scn) :: Parser ()
decl = (newIndent =<< L.indentLevel) *> choice
   [ extern
   , void $ reserved "import" *> _uIden
   , funBind
-- , infixDecl
   ]

extern =
 let _typed = reservedOp ":" *> primType
     doName = iden >>= \i -> addBindName i *> pure i
 in addImport =<< choice
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

--  let super = many $ reservedOp "<:" *> tyName
--  in reserved "class" $> TypeClass <*>
--       tyName <*> many tyVar <*> super <*> pWhere decl
--reserved "instance" $> TypeClassInst
--  <*> tyName <*> some tyName <*> pWhere decl

--pWhere :: Parser a -> Parser [a]
--pWhere pdecl = reserved "where" *> do
--  bracesn ((pdecl <* scn) `sepBy2` symboln ";") <|> do
--    ref <- use indent <* scn
--    lvl <- L.indentLevel
--    local (const lvl) $ indentedItems ref lvl scn pdecl (fail "_")

--fnName = (iden <|> _symbolName) >>= addBindName
funBind = _funBind iden <|> _funBind (parens _symbolName)
_funBind nameParser = mdo
  m    <- nameParser    -- TODO use nameParser not string below
  incArgNest
  iNm  <- addBindName m -- handle recursive references
  addBind $ FunBind m implicits eqns ann -- this must be done before parsing the body (hence mdo)
  implicits  <- choice
    [ reservedOp "::" *>
      bracesn ((iden >>= addArgName) `sepBy` reservedOp ";")
    , pure []
    ]
  ann <- optional $ reservedOp ":" *> tt
  eqns <- case ann of
   Just{} -> choice
    [ lexemen (reservedOp "=") *> ((:[]) . FnMatch [] [] <$> tt)
    , scn *> some (lexemen (string m) *> fnMatch)
    ]
   Nothing -> scn *> do
     (:) <$> fnMatch <*> many (lexemen (string m) *> fnMatch)
  clearLocals

-- TODO this duplicates some code in _funBind
lambda = reservedOp "\\"
  *> (Var . VBind <$> addAnonBindName)
  <* mdo
    incArgNest
    addBind $ FunBind "" [] eqns Nothing
    eqns <- (:[]) <$> ((fnArgs <* lexemen (reservedOp "->")) <*> tt) -- fnMatch
    clearLocals

fnMatch = (fnArgs <* lexemen (reservedOp "=")) <*> tt
fnArgs = let
  implicits = choice
   [ reservedOp "@" *>
       braces ((iden >>= lookupImplicit) `sepBy1` ";")
   , pure []
   ]
  in choice
    [ FnMatch <$> implicits <*> many (lexeme pattern)
--  , InfixMatch <$> (lexeme pat *> parens thisName) <*> many (lexeme pat)
    ]

-- We often need to parse a 2nd token to find out more about the first
-- eg. we have 2 'states' when parsing a tt
-- 1. `maybeApp` we may be parsing a fn app
-- 2. `arg` we are parsing arguments to an app (eg. Lit | parens app ..)
-- infix trains : parse out infix apps assuming equal precedence
tt :: Parser TT = dbg "tt" $ choice
  [ letIn      -- "let"
  , multiIf    -- "if"
  , match      -- "case"
  , tySum      -- " | lab tys
  , lambdaCase -- "\\case"
  , lambda
  , maybeApp >>= \tt -> choice
    [ Proj tt <$ reservedOp "." <*> (iden >>= newFLabel)
    , infixTrain tt
    , pure tt
    ]
  ] -- >>= \exp -> choice [reservedOp ":" $> Typed exp <*> tt , pure exp]
  where
  maybeApp = arg >>= \fn -> choice [App fn <$> some arg , pure fn]
  infixTrain lArg = InfixTrain lArg <$> some ((,) <$> infixName <*> maybeApp)
  arg = dbg "pSingleExp" $ choice
   [ WildCard <$ reserved "_"
   , con
   , iden >>= \i -> choice [label i, lookupBindName i]
   , Lit <$> literalP
   , TyListOf <$> brackets tt
   , parens tt
   ]
  label i = P.Label <$ reservedOp "@" <*> newSLabel i <*> some arg

  tySum = let -- TODO check indent ?
    labeledTTs = (,) <$> (iden >>= newSLabel) <*> many arg
    in TySum <$> some (try (scn *> reservedOp "|" *> lexeme labeledTTs))

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
    multiIf = do _
--    l <- L.indentLevel
--    iB (pure $ L.IndentSome (Just l) (pure . MultiIf) subIf)

  letIn = reserved "let" *> do
    ref <- use indent <* scn
    lvl <- L.indentLevel
--  local (const lvl) $ dbg "letBinds" $ do -- save this indent
--    binds <- BDecls <$> indentedItems ref lvl scn decl (reserved "in")
    indentedItems ref lvl scn funBind (reserved "in")
    reserved "in"
    tt

--caseExpr = do
--  reserved "case"
--  scrut <- tt <* reserved "of"
--  ref <- use indent <* scn
--  l <- L.indentLevel
--  newIndent l *> (Case scrut <$> indentedItems ref l scn alt eof) <* newIndent ref

pattern = singlePattern
singlePattern = dbg "pattern" $ choice
 [ PLit <$> literalP
 , PArg <$> (iden >>= addArgName)
 , PWildCard <$ reserved "_"
 , parens typedPattern
 ]
typedPattern = singlePattern >>= \p -> choice
  [ PTyped p <$ reservedOp ":" <*> tt
  , pure p]

----------------
-- Primitives  -
----------------
-- * llvm types
-- * llvm instructions
primDef = symbol "#!"
primTuple = symbol "#!,"

primType = dbg "primType" $ do try (parens (PrimTuple <$> trivialType `sepBy2` primTuple))
        <|> trivialType
trivialType :: Parser PrimType = (<?> "Builtin Type") $
  primDef *> choice
  [ symbol "Int"      *> (PrimInt <$> L.decimal)
  , symbol "Float"    *> pure (PrimFloat FloatTy)
  , symbol "Double"   *> pure (PrimFloat DoubleTy)
  , symbol "CharPtr"  *> pure (PtrTo $ PrimInt 8)
--  , reserved "ptr"    *> (PtrTo <$> primType)
  ] <|> parens primType

--------------------
-- number parsers --
--------------------
-- needs to return an Exp so we can give the literal a polytype
literalP = lexeme $ choice
 [ Char   <$> charLiteral
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
