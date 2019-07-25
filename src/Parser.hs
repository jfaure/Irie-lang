{-# LANGUAGE MultiWayIf, OverloadedStrings #-}
module Parser where

import ParseSyntax

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr
import Control.Monad (void)
import Data.Void
import Data.List (isInfixOf)
import qualified Data.Text as T
import qualified Data.Text.IO as T.IO
import qualified Data.ByteString.Char8 as C -- so char->Word8

import LLVM.AST hiding (Type, void, Name)
import qualified LLVM.AST (Type, Name)
import LLVM.AST.AddrSpace
-- import LLVM.AST.Type hiding (Type, Void, void)
import LLVM.AST.Float
import Text.Read(readMaybe)
import Data.Maybe (isJust)

import Debug.Trace
import Text.Megaparsec.Debug

type Parser = Parsec Void T.Text

-- A key convention: tokens should parse following whitespace
-- so Parsers can assume no whitespace when they start.

-- Space consumers: scn eats newlines, sc does not.
lineComment = L.skipLineComment ("--")
blockComment = L.skipBlockComment ("{-") ("-}")
scn :: Parser () -- space, newlines
scn = L.space space1 lineComment blockComment
sc :: Parser () -- space
sc = L.space (void $ takeWhile1P Nothing f) lineComment empty
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
reservedName w = (lexeme . try) (string (T.pack w) *> notFollowedBy alphaNumChar)
reservedOp w = lexeme $ try (notFollowedBy (opLetter w) *> string (T.pack w))
  where opLetter :: String -> Parser ()
        opLetter w = void $ choice (string . T.pack <$> longerOps w)
        longerOps w = filter (\x -> isInfixOf w x && x /= w) reservedOps
reserved = reservedName

iden :: Parser Name
iden = (lexeme . try) (p >>= check)
  where
  p = (:) <$> letterChar <*> many alphaNumChar
  check x = if x `elem` reservedNames
            then fail $ "keyword " ++ show x ++ " cannot be an identifier"
            else return (Ident x)

-- lower, upper case first letter of identifiers
lIden, uIden :: Parser Name
lIden = lookAhead lowerChar *> iden -- variables
uIden = lookAhead upperChar *> iden -- constructors / types

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

------------
-- Parser --
------------
-- See ParseSyntax

parseModule :: FilePath -> T.Text
          -> Either (ParseErrorBundle T.Text Void) [Decl]
parseModule = parse (between sc eof parseProg)

parseProg :: Parser [Decl]
parseProg = noIndent decl `sepEndBy` many endLine

name = iden
-- Decl is the top level
-- Most parsers are defined locally here
decl :: Parser Decl
decl = dbg "decl" $ do typeAlias <|> dataDecl <|> infixDecl
   <|> typeClass <|> instDecl <|> defaultDecl
   <|> try typeSigDecl <|> funBind
  where
  typeAlias = TypeAlias <$ reserved "type"
              <*> uIden <* symboln "=" <*> uIden
  dataDecl = do l <- L.indentLevel
                reserved "data"
                tName <- name
                fields <- ((reservedOp "=" *> pData l tName)
                 <|> (reserved "where" *> gadt l tName))
                return $ DataDecl tName TyUnknown fields
    where
    pData l tName = iB (return $ L.IndentMany (Just l) return qualConDecl)
    gadt l tName  = iB (return $ L.IndentMany (Just l) return qualConDecl)

  infixDecl = let pInfix = AssocNone  <$ reserved "infix"
                       <|> AssocRight <$ reserved "infixr"
                       <|> AssocLeft  <$ reserved "infixl"
              in InfixDecl <$> pInfix <*> optional int <*> some name
  typeSigDecl = TypeSigDecl <$> dbg "sig" (name `sepBy` symbol ",")
                            <* reservedOp ":" <*> pType <?> "typeSig"
  funBind = FunBind <$> dbg "funbind" (some (Match <$> name <*> return [] -- many (lexeme pat)
                                 <* reservedOp "=" <*> rhs <*> return Nothing)) -- optional binds))
                  -- <|> infixMatch ?
  typeClass = fail "no typeclass" -- TypeClassDecl <$ (reserved "typeclass")
  instDecl = fail "no instdecl" -- InstDecl Nothing <*> instRule <*> many instDecls
--  where instRule = IRule <*> many tyVarBind <*> instHead
--        instHead = IHCon <*> qName

--        instDecls = fail "_" {- instDecls decl
--                    <|> instType <*> pType <*> pType
--                    <|> instData <*> pType <*> many qualConDecl -}
  defaultDecl = DefaultDecl <$ reserved "default"
                <*> pType <*> pType

qualConDecl :: Parser QualConDecl
qualConDecl = QualConDecl <$> many tyVarBind
          <*> (conDecl <|> infixCon <|> gadtDecl)
  where
  infixCon = fail "unsupported"
  conDecl = ConDecl <$> uIden <*> many pType
  gadtDecl = GadtDecl <$> uIden <*> typeAnn <*> some tyVarBind <*> many fieldDecl
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
indentedItems ref lvl scn p = go where
 go = do
  scn
  pos <- L.indentLevel
  done <- isJust <$> optional eof
  if | pos <= ref || done -> return []
     | pos == lvl         -> (:) <$> p <*> go
     | otherwise          -> L.incorrectIndent EQ lvl pos

pExp :: Parser PExp
pExp = letIn <|> multiIf <|> caseExpr
   <|> Lit <$> literal
   <|> app <|> lambda -- must be tried before var
   <|> Con . UnQual <$> uIden
   <|> Var . UnQual <$> lIden
-- <|> pInfix
   <|> doExpr <|> mdoExpr <|> parens pExp
  where
  pInfix = Ident <$ char '\"' *> manyTill L.charLiteral (char '\"'::Parser Char)
  app = App <$> dbg "papp" pExp <*> some pExp
  lambda = Lambda <$ char '\\' <*> many pat <*> pExp
  letIn = dbg "let" $ do
    ref <- L.indentLevel
    reserved "let"
    scn
    lvl <- L.indentLevel
    binds <- BDecls <$> indentedItems ref lvl scn decl
    reserved "in"
    p <- pExp
    return (Let binds p)
  multiIf = normalIf <|> do
    l <- L.indentLevel
    reserved "if"
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
      <|> PVar <$> uIden
      <|> PLit <$> literal
--    <|> PInfixApp <$> pat <*> (UnQual <$> lIden) <*> pat
      <|> PApp <$> (UnQual <$> lIden) <*> some pat
    )

pType :: Parser Type -- must be a type (eg. after ':')
pType = dbg "ptype" $ do llvmTy <|> forall <|> (TyVar <$> tyVarBind) <|> lifted
        <|> tyOr <|> tyAnd <|> unKnown
  where
  llvmTy = TyLlvm <$> llvmType
  llvmType =
    let mkPtr x = PointerType x (AddrSpace 0)
    in     IntegerType 32 <$ string "Int"
       <|> FloatingPointType DoubleFP <$ string "Double"
       <|> mkPtr (IntegerType 8) <$ string "CharPtr"
       <|> mkPtr (IntegerType 8) <$ string "CStr"
       <|> reserved "ptr" *> (mkPtr <$> llvmType)
       <|> try readLlvmType
       <?> "llvm Type"
  readLlvmType :: Parser LLVM.AST.Type
  readLlvmType = maybe (fail "readLlvmType failed") return =<<
                       (readMaybe <$> manyTill L.charLiteral
                         (satisfy (\x->x==';'||x=='n')))
                 <?> "llvm Type"
  lifted = fail "_"
  tyOr = fail "_"
  tyAnd = fail "_"
  unKnown = TyUnknown <$ reserved "_"

tyVarBind :: Parser TyVarBind
tyVarBind = (\x -> TyVarBind x TyUnknown) <$> lIden :: Parser TyVarBind
forall :: Parser Type
forall = TyForall <$ reserved "forall" <*> some tyVarBind
         <* reservedOp "." <*> pType

typeAnn :: Parser Type
typeAnn = reserved ":" *> (pType <|> return TyUnknown)
