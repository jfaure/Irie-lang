{-# LANGUAGE MultiWayIf, OverloadedStrings #-}
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
import Text.Megaparsec.Debug

-- we need to remember indentation after parsing newlines
-- because we may parse many expressions on a line before it's relevant
type Parser = (ParsecT Void T.Text (ST.State Pos))

-----------
-- Lexer --
-----------
-- A key convention: tokens should parse following whitespace
-- so Parsers can assume no whitespace when they start.

-- Space consumers: scn eats newlines, sc does not.
lineComment = L.skipLineComment "--"
blockComment = L.skipBlockComment "{-" "-}"
scn :: Parser () -- space, newlines. return true if found newline
scn = L.space space1 lineComment blockComment
sc :: Parser () -- space
sc = L.space (void $ takeWhile1P Nothing f) lineComment blockComment
  where f x = x == ' ' || x == '\t'

lexeme, lexemen :: Parser a -> Parser a -- parser then whitespace
lexeme = L.lexeme sc
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

-- lower, upper case first letter of identifiers
lIden, uIden, symbolName :: Parser Name
lIden = lookAhead lowerChar *> iden -- variables
uIden = lookAhead upperChar *> iden -- constructors / types
symbolName = Symbol <$> lexeme (some symbolChar)

qName = lIden

int :: Parser Integer
int = lexeme L.decimal
double :: Parser Double
double = lexeme L.float

-- L.charLiteral handles escaped chars automatically (eg. \n)
charLiteral :: Parser Char
charLiteral = between (single '\'') (single '\'') L.charLiteral
stringLiteral :: Parser String
stringLiteral = char '\"' *> manyTill L.charLiteral (single '\"')

parens, braces :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")
braces = between (symbol "{") (symbol "}")

endLine = lexeme (single '\n')

noIndent = L.nonIndented scn . lexeme
iB = L.indentBlock scn
saveIndent = L.indentLevel >>= put

--sepBy2 :: Alternative m => m a -> m sep -> m [a]
sepBy2 p sep = liftA2 (:) p (some (sep *> p))

dbgToEof = traceShowM =<< (getInput :: Parser T.Text)
d = dbgToEof
db x = traceShowM x *> traceM ": " *> d

------------
-- Parser --
------------
-- See ParseSyntax

parseModule :: FilePath -> T.Text
          -> Either (ParseErrorBundle T.Text Void) [Decl]
parseModule nm txt = evalState doParse (mkPos 0)
  where doParse = runParserT (between sc eof parseProg) nm txt

parseProg :: Parser [Decl]
parseProg = noIndent decl `sepEndBy` many endLine

name = iden
-- Decl is the top level
-- Most parsers are defined locally here
decl :: Parser Decl
decl = saveIndent *> parseDecl
  where
  parseDecl = typeAlias <|> dataDecl <|> infixDecl <|> defaultDecl
   <|> try typeSigDecl  <|> funBind
  typeAlias = TypeAlias <$ reserved "type"
              <*> uIden <* symboln "=" <*> pType
  dataDecl = fail "data unimplemented"
--dataDecl = do l <- L.indentLevel
--              reserved "data"
--              tName <- name
--              fields <- ((reservedOp "=" *> pData l tName)
--               <|> (reserved "where" *> gadt l tName))
--              DataDecl tName TyUnknown (some fields)
    where
    pData l tName = qualConDecl
    gadt l tName  = qualConDecl

  infixDecl = let pInfix = AssocNone  <$ reserved "infix"
                       <|> AssocRight <$ reserved "infixr"
                       <|> AssocLeft  <$ reserved "infixl"
              in InfixDecl <$> pInfix <*> optional int <*> some name
  typeSigDecl = TypeSigDecl <$> dbg "sig" (fnName `sepBy` symbol ",")
                            <* reservedOp ":" <*> pType <?> "typeSig"
    where fnName = name <|> parens symbolName
  funBind = FunBind <$> dbg "funBind" (some (Match <$> name <*> many (lexeme pat)
                        <* reservedOp "=" <*> rhs))
                  -- <|> infixMatch ?
  defaultDecl = DefaultDecl <$ reserved "default"
                <*> pType <*> pType

qualConDecl :: Parser QualConDecl
qualConDecl = QualConDecl <$> many tyVar
          <*> (conDecl <|> infixCon <|> gadtDecl)
  where
  infixCon = fail "unsupported"
  conDecl = ConDecl <$> uIden <*> many pType
  gadtDecl = GadtDecl <$> uIden <*> typeAnn <*> some tyVar <*> many fieldDecl
    where fieldDecl = FieldDecl <$> uIden <*> typeAnn

literal :: Parser Literal
literal = Char <$> charLiteral
      <|> String <$> stringLiteral
      <|> Int <$> int
--      <|> Frac <*> rational

binds :: Parser Binds
binds = BDecls <$> many decl
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
pExp = dbg "pexp" $ do letIn <|> multiIf <|> caseExpr
   <|> Lit <$> literal <|> lambda
   <|> try app -- must be tried before var
   <|> Infix . UnQual <$> pInfix
   <|> someName -- con or app
   <|> doExpr <|> mdoExpr <|> parens pExp
  where
  someName = Con . UnQual <$> uIden <|> Var . UnQual <$> lIden
  pInfix = between (char '"') (char '"') name
       <|> symbolName
  app = App <$> dbg "papp" someName <*> some pExp
  lambda = Lambda <$ char '\\' <*> many pat <* symbol "->" <*> pExp
  letIn = dbg "let" $ do
    reserved "let"
    ref <- get -- reference indentation
    scn
    lvl <- L.indentLevel
    put lvl -- save this indent
    binds <- BDecls <$> indentedItems ref lvl scn decl (reserved "in")
    reserved "in"
    p <- pExp
    return (Let binds p)
  multiIf = normalIf <|> do
    reserved "if"
    l <- L.indentLevel
    iB (return $ L.IndentSome (Just l) (return . MultiIf) subIf)
      where
      normalIf = do {
        reserved "if" ; ifE <- pExp ;
        reserved "then" ; thenE <- pExp ;
        reserved "else" ; elseE <- pExp ;
        return (MultiIf [(ifE, thenE), (WildCard, elseE)]) }
      subIf = (,) <$ reservedOp "|" <*> pExp
              <* reservedOp "=" <*> pExp

  caseExpr = Case <$ reserved "case" <*> pExp <*> many alt
  typeSig e = reserved ":" *> pType >>= \t -> return (TypeSig e t)
  typeExp = TypeExp <$> pType
  asPat = AsPat <$> lIden <* reservedOp "@" <*> pat
  doExpr = fail "_"
  mdoExpr = fail "_"

rhs :: Parser Rhs
rhs = UnGuardedRhs <$> dbg "rhs" pExp

alt :: Parser Alt
alt = Alt <$ reserved "->" <*> pat <*> rhs
pat :: Parser Pat
pat = dbg "pat" (
          PWildCard <$ reserved "_"
      <|> PLit <$> literal
      <|> PVar <$> dbg "patIden" lIden
      <|> PApp <$> (UnQual <$> lIden) <*> some pat
--    <|> PInfixApp <$> pat <*> (UnQual <$> lIden) <*> pat
    )

pType :: Parser Type -- must be a type (eg. after ':')
pType = dbg "ptype" $ do
 try forall <|> try tyArrow <|> singleType
 where tyArrow = TyArrow <$> dbg "arrow" (singleType `sepBy2` symbol "->")

singleType :: Parser Type
singleType = llvmTy <|> (TyVar <$> tyVar) <|> (TyName <$> uIden)
         <|> lifted <|> unKnown
  where
  llvmTy = TyLlvm <$> llvmType
  lifted = fail "_"
  unKnown = TyUnknown <$ reserved "_"
forall :: Parser Type
forall = TyForall <$> (ForallAnd <$> try (singleType `sepBy2` symbol "&")
                   <|> ForallOr  <$> singleType `sepBy2` symbol "|")


tyVar :: Parser Name
tyVar = lIden

typeAnn :: Parser Type
typeAnn = reserved ":" *> pType <|> return TyUnknown

llvmType :: Parser (LLVM.AST.Type)
llvmType =
  let mkPtr x = PointerType x (AddrSpace 0)
  in lexeme (
      IntegerType 32 <$ string "Int"
     <|> FloatingPointType DoubleFP <$ string "Double"
     <|> mkPtr (IntegerType 8) <$ string "CharPtr"
     <|> mkPtr (IntegerType 8) <$ string "CStr"
     <|> reserved "ptr" *> (mkPtr <$> llvmType)
     <|> try readLlvmType)
     <?> "llvm Type"
  where
  readLlvmType :: Parser LLVM.AST.Type
  readLlvmType = maybe (fail "readLlvmType failed") return =<<
                       (readMaybe <$> manyTill L.charLiteral
                         (satisfy (\x->x==';'||x=='n')))
                 <?> "llvm Type"
