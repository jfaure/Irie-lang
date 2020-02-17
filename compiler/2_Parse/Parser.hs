{-# LANGUAGE OverloadedStrings , TemplateHaskell #-}
{-# LANGUAGE LambdaCase, ScopedTypeVariables , MultiWayIf , StandaloneDeriving #-}
module Parser where

{-
  Parsing is responsible for:
  * converting all names to indexes into various vectors
    1. VBind:   top-level let bindings
    2. VLocal:  lambda-bound arguments (these don't index anything)
    3. VExtern: out-ofscope variables to be resolved later
  * Lifting all let-bindings (incl resolving free-vars)
  * figuring out (relative) universes from context
  * identifying functions that return terms
-}

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
 , _nArgs    :: Int
 , _nImports :: Int
 , _moduleWIP  :: Module
}
makeLenses ''ParseState

type Parser = ParsecT Void T.Text (ST.State ParseState)

-- Boilerplate name conversions
newIndent new = indent .= new
addBind b     = moduleWIP . bindings %= (b:)
addImport i   = moduleWIP . imports  %= (i:)

il = M.insertLookupWithKey (\k new old -> old)
insertOrRetrieve h mp = let sz = M.size mp in case il h sz mp of 
  (Just x, mp) -> (x  , mp)
  (_,mp)       -> (sz , mp)

pd = moduleWIP . parseDetails
addArgName , addBindName , addImportName:: T.Text -> Parser IName
addArgName    h = pd . hNameArgs    %%= insertOrRetrieve h
addBindName   h = pd . hNameBinds   %%= insertOrRetrieve h
addImportName h = pd . hNameImports %%= insertOrRetrieve h

rmImportName h = moduleWIP . parseDetails . hNameImports %= M.delete h
rmBindName h = (moduleWIP . parseDetails . hNameBinds) %= M.delete h

newFLabel h = moduleWIP . parseDetails . fields %%= insertOrRetrieve h
fLabel    h = _
newSLabel h = moduleWIP . parseDetails . labels %%= insertOrRetrieve h
sLabel    h = _
-- try first the argmap, then the bindmap, finally assume the name is imported
lookupBindName h = do
  pd <- use $ moduleWIP . parseDetails
  case M.lookup h (pd ^. hNameArgs) of
    Just arg  -> pure $ VLocal arg
    Nothing   -> case M.lookup h (pd ^. hNameBinds) of
      Just bind -> pure $ VBind bind
      Nothing   -> VExtern <$> addImportName h

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
reservedOps   = T.words "= -> | : #! . ;"
reservedNames = T.words "type data record class extern externVarArg let rec in where case of _ import require Set"
reservedName w = (lexeme . try) (string (T.pack w) *> notFollowedBy alphaNumChar)
reservedOp w = lexeme (notFollowedBy (opLetter w) *> string w)
  where opLetter :: T.Text -> Parser ()
        opLetter w = void $ choice (string <$> longerOps w)
        longerOps w = filter (\x -> T.isInfixOf w x && x /= w) reservedOps
reserved = reservedName

-----------
-- Names --
-----------
-- in general, we have to use try in case we parse part of a reserved word
iden :: Parser HName = try $ lexeme (p >>= check) where
  p :: Parser T.Text
  p = lookAhead letterChar *> takeWhileP Nothing isAlphaNum
  check x = if x `elem` reservedNames
            then fail $ "keyword "++show x++" cannot be an identifier"
            else pure x
_lIden, _uIden, pModuleName :: Parser HName
_lIden = lookAhead lowerChar *> iden
_uIden = lookAhead upperChar *> iden
newLIden = _lIden >>= addBindName
newUIden = _uIden >>= addBindName
pModuleName = _uIden

_symbolName = lexeme (p >>= check) where
  p :: Parser T.Text
  p = takeWhile1P Nothing ((`T.any` symbolChars) . (==))
  check x = if x `elem` reservedOps
            then fail $ "reserved Symbol: "++show x ++" cannot be an identifier"
            else pure  x
symbolName :: Parser IName = addBindName =<< _symbolName

infixName = between (symbol "`") (symbol "`") newLIden <|> symbolName
qualifier = newLIden <|> newUIden -- not a symbol
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
p `sepBy2` sep = (:) <$> p <*> (some (sep *> p))

endLine = lexeme (single '\n')

-- indentation shortcuts
noIndent = L.nonIndented scn . lexeme
iB = L.indentBlock scn
--svIndent f = L.indentLevel >>= \s -> local (const s) f
svIndent f = L.indentLevel >>= newIndent


--debug functions
dbgToEof = traceShowM =<< (getInput :: Parser T.Text)
d = dbgToEof
db x = traceShowM x *> traceM ": " *> d

------------
-- Parser --
------------
-- See ParseSyntax
parseModule :: FilePath -> T.Text
            -> Either (ParseErrorBundle T.Text Void) Module
  = \nm txt ->
  let startModule = Module {
          _moduleName = T.pack nm
        , _imports = []
        , _bindings= []
        , _locals  = []
        , _parseDetails = ParseDetails {
             _hNameBinds   = M.empty
           , _hNameArgs    = M.empty
           , _hNameImports = M.empty
           , _fields       = M.empty
           , _labels       = M.empty
        }
      }
  in runParserT (scn *> doParse *> eof *> use moduleWIP) nm txt
  `evalState` ParseState {
       _indent = mkPos 1
     , _nBinds   = 0
     , _nArgs    = 0
     , _nImports = 0
     , _moduleWIP  = startModule
     }

--parseProg :: Parser [Decl]
-- = noIndent decl `sepEndBy` many endLine

-- group declarations as they are parsed
doParse :: Parser ()
doParse = void $ decl `sepEndBy` (endLine *> scn)
decl = (newIndent =<< L.indentLevel) *> choice
   [ importDecl
   , bindDecl
   ]

-- infixDecl ?
importDecl = void $ reserved "import" *> pModuleName
bindDecl = choice
 [ extern
 , funBind
-- , infixDecl
 ]

extern =
 let _typed = reservedOp ":" *> primType
 in addBind =<< ExternBind <$> choice
 [ Extern   <$ reserved "extern"      <*> newLIden <*> _typed
 , ExternVA <$ reserved "externVarArg"<*> newLIden <*> _typed
 ]
--infixDecl = let
--  pInfix = choice
--    [ reserved "infix"  $> AssocNone
--    , reserved "infixr" $> AssocRight
--    , reserved "infixl" $> AssocLeft]
--  opNames = (\x->[x]) <$> symbolName --`sepBy` symbol ","
--  in InfixDecl <$> pInfix <*> optional (lexeme L.decimal) <*> opNames

fnName = newLIden <|> parens symbolName

--  let super = many $ reservedOp "<:" *> tyName
--  in reserved "class" $> TypeClass <*>
--       tyName <*> many tyVar <*> super <*> pWhere decl
--reserved "instance" $> TypeClassInst
--  <*> tyName <*> some tyName <*> pWhere decl

--pWhere x = fail "no where" :: Parser [Decl]
--pWhere :: Parser Decl -> Parser [Decl]
--pWhere pdecl = reserved "where" *> do
--  bracesn ((decl <* scn) `sepBy2` symboln ";") <|> do
--    ref <- ask <* scn
--    lvl <- L.indentLevel
--    local (const lvl) $ indentedItems ref lvl scn pdecl (fail "_")

funBind = _funBind iden <|> _funBind (parens _symbolName)
_funBind nameParser = do
    m    <- nameParser
    iNm  <- addBindName m -- need to handle recursive references
    exps <- liftA2 (:) (fnMatch (pure ())) (many (fnMatch nameParser))
    --(exps , letBounds) <- unzip <$> tt
    addBind =<< FunBind exps <$> optional (reservedOp ":" *> tt)
--  mapM addBind (concat letBounds)

fnMatch thisName = dbg "match" $ do
  args <- choice
    [ FnMatch <$> many (thisName *> lexeme pattern)
--  , InfixMatch <$> (lexeme pat *> parens thisName) <*> many (lexeme pat)
    ] <* reservedOp "="
  args <$> tt

-- needs to return an Exp so we can give the literal a polytype
literalExp :: Parser TT = Lit <$> literalP
literalP = lexeme $ choice
 [ Char   <$> charLiteral
 , String <$> stringLiteral
 , numP
 ]

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

-- Note. we have 2 'states' when parsing a tt
-- 1. `maybeApp` we may parse a fn app
-- 2. `arg` we are parsing arguments to an app. (don't parse another app except between parens/let..)
-- infix trains are also possible: for now simply parse out infix apps assuming equal precedence
tt :: Parser TT = dbg "tt" $ choice
  [ letIn
  , multiIf
  , match
  , maybeApp >>= \app -> choice
    [ Proj app <$ reservedOp "." <*> (fLabel =<< iden) -- record projection (access)
    , infixTrain app
    , pure app
    ]
  ] >>= \exp -> choice [reservedOp ":" $> Typed exp <*> tt , pure exp]
  where
  maybeApp = arg >>= \fn -> choice [App fn <$> some arg , pure fn]
  infixTrain lArg = InfixTrain lArg <$> some ((,) <$> qName infixName <*> maybeApp)
  arg = dbg "pSingleExp" $ choice
   [ WildCard <$ reserved "_"
   , termPrim
   , con
   , label
   , try iden >>= lookupBindName
   , parens tt
   ]
  label = P.Label <$> try (iden >>= newSLabel) <*> braces tt
  con = let
    fieldDecl = (,) <$> (newFLabel =<< iden) <* reservedOp ":" <*> arg
    in Cons <$> (braces $ fieldDecl `sepBy1` reservedOp ";")
  match = Match <$> sLabel tt `sepBy1` reservedOp "|"
  termPrim = choice [literalExp , PrimOp <$> dbg "primInstr" primInstr]
  typePrim = choice
   [ TyPrim  <$> primType
-- , TyArrow <$> try (liftA2 (:) tt (some (arg <* reservedOp "->")))
   ]
--lambda = Abs <$ char '\\' <*> many pat <* symbol "->" <*> tt
--lambdaCase = LambdaCase <$> (char '\\' <* reserved "case"
--                                       *> many (alt <* scn))
  multiIf = reserved "if" *> choice [normalIf , multiIf]
    where
    normalIf = do
      ifThen <- (,) <$> tt <* reserved "then" <*> tt
      elseE  <- reserved "else" *> tt
      pure (MultiIf [ifThen, (WildCard, elseE)])
    subIf = (,) <$ reservedOp "|" <*> tt <* reservedOp "=" <*> tt
    multiIf = do
      l <- L.indentLevel
      iB (pure $ L.IndentSome (Just l) (pure . MultiIf) subIf)

-- need to lift bindings ?
  letIn = reserved "let" *> fail "nolet"
--   reserved "let" *> do
--    ref <- use indent <* scn
--    lvl <- L.indentLevel
--    local (const lvl) $ dbg "letBinds" $ do -- save this indent
----    binds <- BDecls <$> indentedItems ref lvl scn decl (reserved "in")
--      pTree <- doParseTree ref lvl (reserved "in")
--      reserved "in"
--      Let pTree <$> tt
  -- it's assumed later that there is at least one if alt
--caseExpr = do
--  reserved "case"
--  scrut <- tt <* reserved "of"
--  ref <- use indent <* scn
--  l <- L.indentLevel
--  newIndent l *> (Case scrut <$> indentedItems ref l scn alt eof) <* newIndent ref

singlePattern = dbg "pattern" $ choice
 [ PLit <$> literalP
 , PArg <$> (iden >>= addArgName)
 , PWildCard <$ reserved "_"
 , parens pattern
 ]
pattern = singlePattern >>= \p -> choice
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

primInstr :: Parser PrimInstr
primInstr = (<?> "Builtin Instr") $
  primDef *> choice
  [ IntInstr   <$> intInstr
  , NatInstr   <$> natInstr
  , FracInstr  <$> fracInstr
  , MemInstr   <$> arrayInstr
  , MkTuple    <$  reserved "MkTuple"
  , Alloc      <$  reserved "alloc"
  , SizeOf     <$  reserved "sizeof"
  ]
  where
  intInstr = choice
    [ symbol "add"  $> Add
    , symbol "sub"  $> Sub
    , symbol "mul"  $> Mul
    , symbol "sdiv" $> SDiv
    , symbol "srem" $> SRem
    , symbol "icmp" $> ICmp
    , symbol "and"  $> And
    , symbol "or"   $> Or
    , symbol "xor"  $> Xor
    , symbol "shl"  $> Shl 
    , symbol "shr"  $> Shr]
  natInstr = choice
    [symbol "udiv" $> UDiv
    , symbol "urem" $> URem]
  fracInstr = choice
    [ symbol "fadd"  $> FAdd
    , symbol "fsub"  $> FSub
    , symbol "fmul"  $> FMul
    , symbol "fdiv"  $> FDiv
    , symbol "frem"  $> FRem
    , symbol "fcmp"  $> FCmp]
  arrayInstr = choice
    [ symbol "gep"         $> Gep
    , symbol "extractVal"  $> ExtractVal
    , symbol "insertVal"   $> InsertVal]

--------------------
-- number parsers --
--------------------
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
