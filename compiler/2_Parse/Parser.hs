{-# LANGUAGE OverloadedStrings #-}
module Parser where

import Prim
import ParseSyntax

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad (void)
import Control.Applicative (liftA2)
import Data.Void
import Data.List (isInfixOf)
import qualified Data.Text as T
--import qualified Data.ByteString.Char8 as C -- so ghc realises char ~ Word8
import Control.Monad.State.Strict as ST
import Control.Monad.Reader
import Data.Functor

import Debug.Trace
import qualified Text.Megaparsec.Debug as DBG
dbg i = id -- DBG.dbg i

--located :: Parser (Span -> a) -> Parser a = do
--  start <- getPosition
--  f <- p
--  end <- getPosition
--  pure $ f (Span (sourcePosToPos start) (sourcePosToPos end))

-- we need to save indentation in some expressions
-- because we may parse many expressions on a line before it becomes relevant
type Parser = (ParsecT Void T.Text (Reader Pos))

-----------
-- Lexer --
-----------
-- A key convention: tokens should parse following whitespace
-- `symbol` and `lexeme` do that
-- so Parsers can assume no whitespace when they start.

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
symbol = L.symbol sc . T.pack
symboln = L.symbol scn . T.pack

-- valid symbols in the language
-- all symbol chars = "!\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~"
-- reserved: ():\{}"_'`.
symbolChars = "!#$%&'*+,-/;<=>?@[]^|~" :: String
reservedOps = ["=","->","|",":", "#!", "."]
reservedNames = ["type", "data", "class", "extern", "externVarArg",
                 "let", "in", "case", "of", "_"]
reservedName w = (lexeme . try) (string (T.pack w) *> notFollowedBy alphaNumChar)
reservedOp w = lexeme (notFollowedBy (opLetter w) *> string (T.pack w))
  where opLetter :: String -> Parser ()
        opLetter w = void $ choice (string . T.pack <$> longerOps w)
        longerOps w = filter (\x -> isInfixOf w x && x /= w) reservedOps
reserved = reservedName

iden :: Parser Name
iden = lexeme (p >>= check)
  where
  p = (:) <$> letterChar <*> many alphaNumChar
  check x = if x `elem` reservedNames
            then fail $ "keyword "++show x++" cannot be an identifier"
            else pure (Ident x)

symbolName = check =<< some (satisfy (`elem` symbolChars))
  where
  check x = if x `elem` reservedOps
            then fail $ "reserved Symbol: "++show x ++" cannot be an identifier"
            else pure $ Symbol x

-- Names
lIden, uIden, symbolName :: Parser Name
lIden = lookAhead lowerChar *> iden -- variables
uIden = lookAhead upperChar *> iden -- constructors / types
name = iden
infixName = between (symbol "`") (symbol "`") lIden <|> symbolName
qualifier = lIden <|> uIden -- not a symbol
qName p = lexeme (many (try (qualifier <* reservedOp ".")) >>= \case
  []  -> UnQual <$> p
  nms -> QName nms <$> p)

-- literals
int    :: Parser Integer = lexeme L.decimal
double :: Parser Double  = lexeme L.float
-- L.charLiteral handles escaped chars (eg. \n)
charLiteral :: Parser Char = between (single '\'') (single '\'') L.charLiteral
stringLiteral :: Parser String
  = char '\"' *> manyTill L.charLiteral (single '\"')

parens, braces :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")
braces = between (symbol "{") (symbol "}")

endLine = lexeme (single '\n')

-- indentation shortcuts
noIndent = L.nonIndented scn . lexeme
iB = L.indentBlock scn
--saveIndent = L.indentLevel >>= put
svIndent f = L.indentLevel >>= \s -> local (const s) f

sepBy2 p sep = liftA2 (:) p (some (sep *> p))

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
  let doParse = runParserT (between sc eof parseProg) nm txt
  in Module (Ident nm) <$> runReader doParse (mkPos 0) -- start indent is 0

parseProg :: Parser [Decl]
 = noIndent decl `sepEndBy` many endLine

decl :: Parser Decl -- top level
 = svIndent parseDecl
  where -- must try funBind first (typeSigDecl = _)
  parseDecl = choice [typeAlias, infixDecl, defaultDecl
    , typeClass, typeClassInst, extern, try funBind, typeSigDecl]

  extern = Extern  <$reserved "extern"      <*> name<*reservedOp ":"<*>pType
       <|> ExternVA<$reserved "externVarArg"<*> name<*reservedOp ":"<*>pType
  -- TODO parse GADT style parser ?
  typeAlias :: Parser Decl
  typeAlias = reserved "data" *> doData <|> reserved "type" *> doType
    where
    doData = defOrFun tyData -- "data" parses a tyData
    doType = defOrFun pType  -- "type" parses any alias (not data)
    defOrFun pTy = try (tyFun (TypeExp <$> pTy)) <|> tyDef pTy
    tyFun pTy = TypeFun   <$> tyName <*> some tyVar <* symboln "=" <*> pTy
    tyDef pTy = TypeAlias <$> tyName                <* symboln "=" <*> pTy

  infixDecl = let pInfix = reserved "infix"  $> AssocNone
                       <|> reserved "infixr" $> AssocRight
                       <|> reserved "infixl" $> AssocLeft
              in InfixDecl <$> pInfix <*> optional int <*> some name
  fnName = name <|> parens symbolName

  -- TODO indentation
  pWhere        = reserved "where" *> scn
  typeClass     = reserved "class"    $> TypeClass <*>
                  tyName <* pWhere <*> between (symboln "{") (symboln "}") (some (decl <* scn))
  typeClassInst = reserved "instance" $> TypeClassInst <*>
                  tyName <*> tyName <* pWhere <*> between (symboln "{") (symboln "}") (some (decl <* scn))

  -- Flexible type vars are possible in type signatures
  -- Also dependent types..
  funBind = FunBind <$> some match
  typeSigDecl = (<?> "typeSig") $ do
    fns <- fnName `sepBy` symbol ","
    reservedOp ":"
    ty <- dbg "sig" pType
    boundExp <- optional (try (scn *> symbol "=" *> pExp))
    case boundExp of
      Nothing -> pure $ TypeSigDecl fns ty -- normal typesig
      Just e  -> case fns of        -- scopedTypeVar style binding
        [fnName] -> pure $
                    FunBind [Match fnName [] (UnGuardedRhs (Typed ty e))]
        _        -> fail "multiple function bindings at once"

  defaultDecl = DefaultDecl <$ reserved "default" <*> singleType <*> singleType
  match = (Match <$> (name <|> parens symbolName) <*> many (lexeme pat)
      <|> InfixMatch <$> (lexeme pat) <*> infixName <*> many (lexeme pat))
      <*  reservedOp "=" <*> rhs

-- needs to return an Exp so we can give the literal a polytype
literalExp :: Parser PExp = lexeme $ choice
 [ Lit . Char   <$> charLiteral
 , Lit . String <$> stringLiteral
 , Lit . Frac . toRational <$> try L.float -- can we avoid the try ?
 , Lit . Int    <$> int]

binds :: Parser Binds = BDecls <$> many decl
-- ref = reference indent level
-- lvl = lvl of first indented item (probably lookahead)
indentedItems ref lvl scn p finished = go where
 go = do
  scn
  pos <- L.indentLevel
  lookAhead (eof <|> finished) *> pure [] <|> if
     | pos <= ref -> pure []
     | pos == lvl -> (:) <$> p <*> go
     | otherwise  -> L.incorrectIndent EQ lvl pos

pExp :: Parser PExp = appOrSingle
  where
  appOrSingle = single >>= \fn -> choice
   [ App fn <$> some single
   , infixApp fn
   , pure fn]
  single = dbg "pSingleExp" $ choice
   [ letIn
   , multiIf
   , lambda
   , lambdaCase
   , caseExpr
   , WildCard <$ reserved "_"
   , PrimOp <$> dbg "primInstr" primInstr
-- , doExpr , mdoExpr
   , literalExp
   , try someName
   , parens (try opSection <|> pExp)
   ]
  opSection = SectionR <$> qName infixName <*> pExp
  infixApp lArg = do
      fnInfix <- Infix <$> qName infixName
      rArg <- some pExp
      pure (App fnInfix (lArg:rArg))
  someName = dbg "someName" $ do
    Con . UnQual <$> uIden
    <|> Var <$> qName lIden
    <|> Var <$> try (qName (parens symbolName))
  lambda = Lambda <$ char '\\' <*> many pat <* symbol "->" <*> pExp
  lambdaCase = LambdaCase <$> (char '\\' <* reserved "case" *> many (alt <* scn))
  letIn = do
    reserved "let"
    ref <- ask -- reference indentation
    scn
    lvl <- L.indentLevel
    local (const lvl) $ do -- save this indent
      binds <- BDecls <$> indentedItems ref lvl scn decl (reserved "in")
      reserved "in"
      p <- pExp
      pure (Let binds p)
  -- it's assumed later that there is at least one if alt
  multiIf = normalIf <|> do
    reserved "if"
    l <- L.indentLevel
    iB (pure $ L.IndentSome (Just l) (pure . MultiIf) subIf)
      where
      normalIf = do
        ifE   <- reserved "if"   *> pExp
        thenE <- reserved "then" *> pExp
        elseE <- reserved "else" *> pExp
        pure (MultiIf [(ifE, thenE), (WildCard, elseE)])
      subIf = (,) <$ reservedOp "|" <*> pExp <* reservedOp "=" <*> pExp

  caseExpr = do
    reserved "case"
    scrut <- pExp <* reserved "of"
    ref <- ask
    scn
    lvl <- L.indentLevel
    local (const lvl) $ do
      alts <- indentedItems ref lvl scn alt (fail "_") -- no end condition
      pure $ Case scrut alts
  typeSig e = reserved ":" *> pType >>= \t -> pure (Typed t e)
  typeExp = TypeExp <$> pType
  asPat = AsPat <$> lIden <* reservedOp "@" <*> pat

rhs :: Parser Rhs = UnGuardedRhs <$> dbg "rhs" pExp
alt :: Parser Alt = Alt <$> pat <* reservedOp "->" <*> rhs
pat :: Parser Pat
 = (parens (PTuple <$> singlePat `sepBy2` symbol ",")) <|> singlePat
singlePat = dbg "singlePat" (
      PWildCard <$ reserved "_"
--  <|> literalExp
  <|> PVar <$> dbg "patIden" lIden
  <|> PApp <$> (UnQual <$> uIden) <*> many pat -- constructor
--    <|> PInfixApp <$> pat <*> (UnQual <$> lIden) <*> pat
    )

-----------
-- Types --
-----------
typeAnn  :: Parser Type = reserved ":" *> pType <|> pure TyUnknown
pType :: Parser Type -- must be a type (eg. after ':')
 = dbg "ptype" $ choice
   [ try tyArrow
   , try forall
   , appOrSingle]
   where
   appOrSingle = dbg "app" $ singleType >>= \fn ->
     TyApp fn <$> some singleType <|> pure fn
   tyArrow = TyArrow <$> dbg "arrow" singleType `sepBy2` symbol "->"

singleType :: Parser Type = choice
 [ TyPrim    <$> try primType
 , TyName    <$> uIden
 , TyVar     <$> lIden
 , parens pType
 , TyUnknown <$  reserved "_"]
forall :: Parser Type
 = TyPoly <$> (PolyAnd <$> try (singleType `sepBy2` symbol "&")
            <|> PolyUnion  <$> singleType `sepBy2` symbol "|")

-- Note this only parses data to the right of the '=' !
-- Because to the left there be type functions..
tyData :: Parser Type
 = fail "_" -- TyRecord <$> tyName <*> braces (some namedCon)
 <|> TyData      <$> ((,) <$> tyName <*> many singleType) `sepBy` symboln "|"
 <|> TyInfixData <$> singleType <*> infixName <*> singleType
  where
  namedCon = (,) <$> tyName <*> some (singleType)

tyName   :: Parser Name = uIden
tyVar    :: Parser Name = lIden

----------------
-- Primitives  -
----------------
-- * llvm types
-- * llvm instructions
primDef = symbol "#!"
primTuple = symbol "#!,"

primType = dbg "primType" $ do try (parens (PrimTuple <$> trivialType `sepBy2` primTuple))
        <|> trivialType
trivialType :: Parser PrimType = (<?> "prim Type") $
  primDef *> choice
     [ symbol "Int"      *> (PrimInt <$> L.decimal)
     , symbol "Float"    *> pure (PrimFloat FloatTy)
     , symbol "Double"   *> pure (PrimFloat DoubleTy)
     , symbol "CharPtr"  *> pure (PtrTo $ PrimInt 8)
     , reserved "ptr"    *> (PtrTo <$> primType)
     ] <|> parens primType

primInstr :: Parser PrimInstr
primInstr = primDef *> choice
 [ IntInstr   <$> intInstr
 , NatInstr   <$> natInstr
 , FracInstr  <$> fracInstr
 , MemInstr   <$> arrayInstr
 , MkTuple    <$  reserved "MkTuple"
 ]
  where
  intInstr = choice
    [ symbol "add"  $> Add
    , symbol "sub"  $> Sub
    , symbol "mul"  $> Mul
    , symbol "sdiv" $> SDiv
    , symbol "srem" $> SRem
    , symbol "icmp" $> ICmp]
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
    , symbol "extractVal"  $> ExtractVal <*> L.decimal
    , symbol "insertVal"   $> InsertVal  <*> L.decimal]
