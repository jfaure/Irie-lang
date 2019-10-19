{-# LANGUAGE MultiWayIf, OverloadedStrings, ScopedTypeVariables #-}
module Parser where

import ParseSyntax

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr
import Control.Monad (void)
import Control.Applicative (liftA2)
import Data.Void
import Data.List (isInfixOf)
import qualified Data.Text as T
import qualified Data.Text.IO as T.IO
import qualified Data.ByteString.Char8 as C -- so ghc realises char ~ Word8
import Control.Monad.State.Strict as ST
import Data.Char (isSymbol)

import LLVM.AST hiding (Type, void, Name)
import qualified LLVM.AST (Type, Name)
import LLVM.AST.AddrSpace
-- import LLVM.AST.Type hiding (Type, Void, void)
import LLVM.AST.Float
import Text.Read(readMaybe)
import Data.Maybe (isJust)

import Debug.Trace
--import Text.Megaparsec.Debug
dbg i = id

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

reservedOps = ["*","/","+","-","=","->","|","->",":"]
reservedNames = ["let", "in", "case", "of", "_", "data", "ptr",
                 "type", "extern", "externVarArg"]
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
            else return (Ident x)

-- Names
lIden, uIden, symbolName :: Parser Name
lIden = lookAhead lowerChar *> iden -- variables
uIden = lookAhead upperChar *> iden -- constructors / types
symbolName = Symbol <$> lexeme (some symbolChar)
name = iden
qName = lIden

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
  in evalState doParse (mkPos 0)

parseProg :: Parser [Decl]
 = noIndent decl `sepEndBy` many endLine

decl :: Parser Decl -- top level
 = saveIndent *> parseDecl
  where
  parseDecl = typeAlias <|> dataDecl <|> infixDecl <|> defaultDecl
   <|> try funBind <|> typeSigDecl -- must try funBind first (typeSigDecl = _)
  typeAlias = TypeAlias <$ reserved "type"
              <*> uIden <* symboln "=" <*> pType
  dataDecl = do reserved "data"
                tName <- name
                fields <- (reservedOp "="   *> pDataAlts)
                      <|> (reserved "where" *> pDataAlts)
                pure $ DataDecl tName TyUnknown fields
      where
      pDataAlts = qualConDecl `sepBy` (reserved "|")

  infixDecl = let pInfix = AssocNone  <$ reserved "infix"
                       <|> AssocRight <$ reserved "infixr"
                       <|> AssocLeft  <$ reserved "infixl"
              in InfixDecl <$> pInfix <*> optional int <*> some name
  fnName = name <|> parens symbolName
  typeSigDecl = TypeSigDecl <$> dbg "sig" (fnName `sepBy` symbol ",")
                            <* reservedOp ":" <*> pType <?> "typeSig"
  funBind = FunBind <$> some match <|> do -- type sig on left of ':'
    fNm  <- fnName
    ty   <- reservedOp ":" *> pType
    bind <- reservedOp "=" *> pExp
    pure $ FunBind [Match fNm [] (UnGuardedRhs bind)]
  defaultDecl = DefaultDecl <$ reserved "default"
                <*> pType <*> pType
  match = (Match <$> (name <|> parens symbolName) <*> many (lexeme pat)
      <|> InfixMatch <$> (lexeme pat) <*> symbolName <*> many (lexeme pat))
      <*  reservedOp "=" <*> rhs

qualConDecl :: Parser QualConDecl = QualConDecl
  <$> many tyVar
  <*> (conDecl <|> infixCon <|> gadtDecl)
  where
  infixCon = fail "unsupported"
  conDecl = ConDecl <$> uIden <*> many pType
  gadtDecl = GadtDecl <$> uIden <*> typeAnn <*> some tyVar <*> many fieldDecl
    where fieldDecl = FieldDecl <$> uIden <*> typeAnn

literal :: Parser Literal
 =     Char   <$> charLiteral
   <|> String <$> stringLiteral
   <|> Int    <$> int
--      <|> Frac <*> rational

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
  =   try lambda <|> lambdaCase
  <|> notFollowedBy app *> arg
  <|> app -- must be tried before var (and must consume all it's args)
  <|> (parens pExp)
  where
  arg = letIn <|> multiIf <|> caseExpr
        <|> WildCard <$ reserved "_"
        <|> (Infix . UnQual <$> pInfix)
        <|> doExpr <|> mdoExpr
        <|> Lit <$> literal <|> someName
        <|> parens pExp

  someName = dbg "someName" $ do Con . UnQual <$> uIden
         <|> Var . UnQual <$> lIden
         <|> Var . UnQual <$> try (parens symbolName)
  pInfix = between (char '`') (char '`') name
       <|> symbolName
  app = App <$> someName <*> some arg
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
  typeSig e = reserved ":" *> pType >>= \t -> return (TypeSig e t)
  typeExp = TypeExp <$> pType
  asPat = AsPat <$> lIden <* reservedOp "@" <*> pat
  doExpr = fail "_"
  mdoExpr = fail "_"

rhs :: Parser Rhs = UnGuardedRhs <$> dbg "rhs" pExp
alt :: Parser Alt = Alt <$> pat <* reserved "->" <*> rhs
pat :: Parser Pat
 = dbg "pat" (
      PWildCard <$ reserved "_"
  <|> PLit <$> literal
  <|> PVar <$> dbg "patIden" lIden
  <|> PApp <$> (UnQual <$> uIden) <*> many pat -- constructor
-- <|> PApp <$> (UnQual <$> lIden) <*> some pat
--    <|> PInfixApp <$> pat <*> (UnQual <$> lIden) <*> pat
    )

pType :: Parser Type -- must be a type (eg. after ':')
 = dbg "ptype" $ do
 try forall <|> try tyArrow <|> singleType <|> parens pType
   where
   tyArrow = TyArrow <$> dbg "arrow" (singleType `sepBy2` symbol "->")

singleType :: Parser Type
 = llvmTy <|> (TyName <$> uIden)
          <|> unKnown <|> parens pType
  where
  llvmTy = TyLlvm <$> llvmType
  unKnown = TyUnknown <$ reserved "_"
forall :: Parser Type
 = TyForall <$> (ForallAnd <$> try (singleType `sepBy2` symbol "&")
            <|> ForallOr  <$> singleType `sepBy2` symbol "|")

tyVar    :: Parser Name = lIden
typeAnn  :: Parser Type = reserved ":" *> pType <|> return TyUnknown
llvmType :: Parser (LLVM.AST.Type) =
  let mkPtr x = PointerType x (AddrSpace 0)
  in lexeme (
         IntegerType 32 <$ symbol "Int"
     <|> FloatingPointType DoubleFP <$ symbol "Double"
     <|> mkPtr (IntegerType 8) <$ symbol "CharPtr"
     <|> mkPtr (IntegerType 8) <$ symbol "CStr"
     <|> reserved "ptr" *> (mkPtr <$> llvmType)
     <|> try readLlvmType)
     <?> "llvm Type"
  where
  readLlvmType :: Parser LLVM.AST.Type
   = maybe (fail "no parse: read : LLVM.AST.Type") return =<<
           (readMaybe <$> manyTill L.charLiteral
           (satisfy (\x->x==';'||x=='n')))
           <?> "llvm Type"
