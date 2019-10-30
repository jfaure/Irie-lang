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

import Debug.Trace
-- import Text.Megaparsec.Debug
dbg i = id

($>) = flip (<$) -- seems obtuse to import Data.Functor just for this

--located :: Parser (Span -> a) -> Parser a = do
--  start <- getPosition
--  f <- p
--  end <- getPosition
--  return $ f (Span (sourcePosToPos start) (sourcePosToPos end))

-- we need to save indentation in some expressions
-- because we may parse many expressions on a line before it becomes relevant
type Parser = (ParsecT Void T.Text (ST.State Pos))

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
reservedName w = (lexeme . try) (string (T.pack w)
                 *> notFollowedBy alphaNumChar)
reservedOp w = lexeme $ try (notFollowedBy (opLetter w)
               *> string (T.pack w))
  where opLetter :: String -> Parser ()
        opLetter w = void $ choice (string . T.pack <$> longerOps w)
        longerOps w = filter (\x -> isInfixOf w x && x /= w) reservedOps
reserved = reservedName

iden :: Parser Name
iden = (lexeme . try) (p >>= check)
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
saveIndent = L.indentLevel >>= put

--sepBy2 :: Alternative m => m a -> m sep -> m [a]
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
            -> Either (ParseErrorBundle T.Text Void) [Decl]
  = \nm txt ->
  let doParse = runParserT (between sc eof parseProg) nm txt
  in evalState doParse (mkPos 0) -- start indent is 0

parseProg :: Parser [Decl]
 = noIndent decl `sepEndBy` many endLine

decl :: Parser Decl -- top level
 = saveIndent *> parseDecl
  where
  parseDecl = typeAlias <|> infixDecl <|> defaultDecl <|>
    typeClass <|> typeClassInst <|>
    extern <|>
    try funBind <|> typeSigDecl -- must try funBind first (typeSigDecl = _)

  extern = Extern  <$reserved "extern"      <*> name<*reservedOp ":"<*>pType
       <|> ExternVA<$reserved "externVarArg"<*> name<*reservedOp ":"<*>pType
  -- TODO GADT style parser ?
  typeAlias :: Parser Decl
  typeAlias = reserved "data" *> doData <|> reserved "type" *> doType
    where
    doData = defOrFun tyData -- "data" parses a tyData
    doType = defOrFun pType  -- "type" parses any alias (not data)
    defOrFun pTy = try tyFun <|> tyDef pTy
    tyFun =     TypeFun   <$> tyName <*> some tyVar <* symboln "=" <*> pExp
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
  typeSigDecl = (<?> "typeSig") $ do
    fns <- fnName `sepBy` symbol ","
    reservedOp ":"
    ty <- pType
    boundExp <- optional (try (scn *> symbol "=" *> pExp))
    case boundExp of
      Nothing -> pure $ TypeSigDecl fns ty -- normal typesig
      Just e  -> case fns of        -- scopedTypeVar style binding
        [fnName] -> pure $
                    FunBind [Match fnName [] (UnGuardedRhs (Typed ty e))]
        _        -> fail "multiple function bindings at once"

  funBind = FunBind <$> some match

  defaultDecl = DefaultDecl <$ reserved "default"
                <*> pType <*> pType
  match = (Match <$> (name <|> parens symbolName) <*> many (lexeme pat)
      <|> InfixMatch <$> (lexeme pat) <*> infixName <*> many (lexeme pat))
      <*  reservedOp "=" <*> rhs

-- needs to return an Exp so we can give the literal a polytype
literalExp :: Parser PExp = lexeme $ do
     Typed (TyPrim (PrimInt 8))           . Lit . Char   <$> charLiteral
 <|> Typed (TyPrim (PrimArr (PrimInt 8))) . Lit . String <$> stringLiteral
 <|> Typed (TyName (Ident "Num"))         . Lit . Frac . toRational <$> try L.float
 <|> Typed (TyName (Ident "Num"))         . Lit . Int    <$> int

binds :: Parser Binds = BDecls <$> many decl
-- ref = reference indent level
-- lvl = lvl of first indented item (probably lookahead)
indentedItems ref lvl scn p finished = go where
 go = do
  scn
  pos <- L.indentLevel
  lookAhead (eof <|> finished) *> return [] <|> if
     | pos <= ref -> return []
     | pos == lvl -> (:) <$> p <*> go
     | otherwise  -> L.incorrectIndent EQ lvl pos

-- don't save indent here, use the state indent saved by parseDecl
pExp :: Parser PExp
  =   lambda <|> lambdaCase
-- <|> notFollowedBy app *> arg -- notFollowedBy infixApp *> arg
-- <|> app -- must be tried before var (and must consume all it's args)
  <|> try app
  <|> try infixApp
  <|> arg
  <|> dbg "parense" (parens pExp)
  where
  arg = letIn <|> multiIf <|> caseExpr
        <|> WildCard <$ reserved "_"
        <|> PrimOp <$> primInstr
--      <|> doExpr <|> mdoExpr
        <|> try literalExp
        <|> someName
        <|> try opSection
        <|> parens pExp
  opSection = parens $ do
    SectionL <$> try pExp <*> qName infixName
    <|> SectionR <$> qName infixName <*> pExp
  infixApp = try $ do
      l <- arg
      fnInfix <- Infix <$> qName infixName
      r <- some arg
      pure (App fnInfix (l:r))
  someName = dbg "someName" $ do
    Con . UnQual <$> uIden
    <|> Var <$> qName lIden
    <|> Var <$> try (qName (parens symbolName))
  app = dbg "app" $ do App <$> someName <*> some arg
  lambda = Lambda <$ char '\\' <*> many pat <* symbol "->" <*> pExp
  lambdaCase = LambdaCase <$> (char '\\' <* reserved "case" *> many (alt <* scn))
  letIn = do
    reserved "let"
    ref <- get -- reference indentation
    scn
    lvl <- L.indentLevel
    put lvl -- save this indent
    binds <- BDecls <$> indentedItems ref lvl scn decl (reserved "in")
    reserved "in"
    p <- pExp
    put ref -- restore indent
    return (Let binds p)
  -- it's assumed later that there is at least one if alt
  multiIf = normalIf <|> do
    reserved "if"
    l <- L.indentLevel
    iB (return $ L.IndentSome (Just l) (return . MultiIf) subIf)
      where
      normalIf = do
        ifE   <- reserved "if"   *> pExp
        thenE <- reserved "then" *> pExp
        elseE <- reserved "else" *> pExp
        pure (MultiIf [(ifE, thenE), (WildCard, elseE)])
      subIf = (,) <$ reservedOp "|" <*> pExp
              <* reservedOp "=" <*> pExp

  caseExpr = do
    reserved "case"
    scrut <- pExp <* reserved "of"
    ref <- get
    scn
    lvl <- L.indentLevel
    put lvl
    alts <- indentedItems ref lvl scn alt (fail "_") -- no end condition
    put ref
    pure $ Case scrut alts
  typeSig e = reserved ":" *> pType >>= \t -> return (Typed t e)
  typeExp = TypeExp <$> pType
  asPat = AsPat <$> lIden <* reservedOp "@" <*> pat
--doExpr = fail "_"
--mdoExpr = fail "_"

rhs :: Parser Rhs = UnGuardedRhs <$> dbg "rhs" pExp
alt :: Parser Alt = Alt <$> pat <* reservedOp "->" <*> rhs
pat :: Parser Pat
 = dbg "pat" (
      PWildCard <$ reserved "_"
--  <|> literalExp
  <|> PVar <$> dbg "patIden" lIden
  <|> PApp <$> (UnQual <$> uIden) <*> many pat -- constructor
--    <|> PInfixApp <$> pat <*> (UnQual <$> lIden) <*> pat
    )

-----------
-- Types --
-----------
typeAnn  :: Parser Type = reserved ":" *> pType <|> return TyUnknown
pType :: Parser Type -- must be a type (eg. after ':')
 = dbg "ptype" $ do
 try forall <|> try tyArrow <|> singleType <|> parens pType
   where
   tyArrow = TyArrow <$> dbg "arrow" (singleType `sepBy2` symbol "->")

singleType :: Parser Type
 = TyPrim <$> primType <|>
   TyName <$> uIden    <|>
   unKnown             <|>
   parens pType
  where
  unKnown = TyUnknown <$ reserved "_"
forall :: Parser Type
 = TyForall <$> (ForallAnd <$> try (singleType `sepBy2` symbol "&")
            <|> ForallOr  <$> singleType `sepBy2` symbol "|")

-- Note this only parses data to the right of the '=' !
-- Because to the left there be type functions..
tyData :: Parser Type
 = fail "_" -- TyRecord <$> tyName <*> braces (some namedCon)
 <|> TyData      <$> ((,) <$> tyName <*> many singleType) `sepBy1` symboln "|"
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

primType :: Parser PrimType = (<?> "prim Type") $
  primDef *> (
         symbol "Int"      *> (PrimInt <$> L.decimal)
     <|> symbol "Float"    *> pure (PrimFloat FloatTy)
     <|> symbol "Double"   *> pure (PrimFloat DoubleTy)
     <|> symbol "CharPtr"  *> pure (PtrTo $ PrimInt 8)
     <|> reserved "ptr"    *> (PtrTo <$> primType)
--   <|> reserved "extern" $> Extern <*> primType `sepBy` symbol "->"
     )

primInstr :: Parser PrimInstr
primInstr = primDef *> (
 IntInstr   <$> intInstr  <|>
 NatInstr   <$> natInstr  <|>
 FracInstr  <$> fracInstr <|>
 MemInstr   <$> arrayInstr
 )
  where
  intInstr =
      symbol "add"  $> Add  <|>
      symbol "sub"  $> Sub  <|>
      symbol "mul"  $> Mul  <|>
      symbol "sdiv" $> SDiv <|>
      symbol "srem" $> SRem <|>
      symbol "icmp" $> ICmp
  natInstr =
      symbol "udiv" $> UDiv <|>
      symbol "urem" $> URem
  fracInstr =
      symbol "fadd"  $> FAdd <|>
      symbol "fsub"  $> FSub <|>
      symbol "fmul"  $> FMul <|>
      symbol "fdiv"  $> FDiv <|>
      symbol "frem"  $> FRem <|>
      symbol "fcmp"  $> FCmp
  arrayInstr =
      symbol "gep"         $> Gep        <|>
      symbol "extractval"  $> ExtractVal <|>
      symbol "insertval"   $> InsertVal
