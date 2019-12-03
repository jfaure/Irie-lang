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
import Data.Char (isAlphaNum)
import qualified Data.Vector as V -- for groupDecls

import Debug.Trace
import qualified Text.Megaparsec.Debug as DBG
dbg i = id
-- dbg i = DBG.dbg i

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
reservedOps   = ["=","->","|",":", "#!", "."]
reservedNames = T.pack <$>
 ["type", "data", "record", "class", "extern", "externVarArg"
 , "let", "rec", "in", "where", "case", "of", "_"
 , "import", "require"]
reservedName w = (lexeme . try) (string (T.pack w) *> notFollowedBy alphaNumChar)
reservedOp w = lexeme (notFollowedBy (opLetter w) *> string (T.pack w))
  where opLetter :: String -> Parser ()
        opLetter w = void $ choice (string . T.pack <$> longerOps w)
        longerOps w = filter (\x -> isInfixOf w x && x /= w) reservedOps
reserved = reservedName

-- have to use try in case we parse part of a reserved word
iden :: Parser Name = try $ lexeme (p >>= check) where
  p :: Parser T.Text
  p = lookAhead letterChar *> takeWhileP Nothing isAlphaNum
  check x = if x `elem` reservedNames
            then fail $ "keyword "++show x++" cannot be an identifier"
            else pure (Ident x)

symbolName :: Parser Name = lexeme (p >>= check) where
  p :: Parser T.Text
  p = takeWhile1P Nothing (`elem` symbolChars)
  check x = if x `elem` (T.pack <$> reservedOps)
            then fail $ "reserved Symbol: "++show x ++" cannot be an identifier"
            else pure $ Symbol x

-- Names
lIden, uIden, name, pModuleName :: Parser Name
lIden = lookAhead lowerChar *> iden -- variables
uIden = lookAhead upperChar *> iden -- constructors / types
name = iden
pModuleName = uIden
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

parens, braces, bracesn :: Parser a -> Parser a
parens  = between (symbol "(") (symbol ")")
braces  = between (symbol "{") (symbol "}")
bracesn = between (symboln "{") (symboln "}")

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
      startIndent = mkPos 0
  in -- Module (Ident $ T.pack nm) <$> runReader doParse startIndent
     mkModule (Ident $ T.pack nm) .groupDecls
     <$> runReader doParse startIndent

mkModule nm (p_TyAlias, p_TyFuns, p_TyClasses, p_TyClassInsts
       , p_TopSigs, p_TopBinds, p_Fixities
       , p_defaults, p_externs, p_imports)
  = Module nm $ ParseTree
      p_TyAlias p_TyFuns p_TyClasses p_TyClassInsts
      p_TopSigs p_TopBinds p_Fixities
      p_defaults p_externs p_imports

type D = V.Vector Decl
type Tuples = (D,D,D,D,D,D,D,D,D,D)
-- Careful! groupDecls output order, would be nice to have subtyping
groupDecls :: [Decl] -> Tuples
groupDecls parsedTree = mapTuple10 V.fromList $
 foldr f ([],[],[],[],[],[],[],[],[],[]) parsedTree
  where
  mapTuple10 z (a,b,c,d,e,f,g,h,i,j)
    = (z a,z b,z c,z d,z e,z f,z g,z h,z i,z j)
  f x (a,b,c,d,e,f,g,h,i,j) = case x of
    TypeAlias{}     -> (x:a,b,c,d,e,f,g,h,i,j)
    TypeFun{}       -> (a,x:b,c,d,e,f,g,h,i,j)
    TypeClass{}     -> (a,b,x:c,d,e,f,g,h,i,j)
    TypeClassInst{} -> (a,b,c,x:d,e,f,g,h,i,j)

    TypeSigDecl{}   -> (a,b,c,d,x:e,f,g,h,i,j)
    FunBind{}       -> (a,b,c,d,e,x:f,g,h,i,j)
    InfixDecl{}     -> (a,b,c,d,e,f,x:g,h,i,j)

    DefaultDecl{}   -> (a,b,c,d,e,f,g,x:h,i,j)
    Extern{}        -> (a,b,c,d,e,f,g,h,x:i,j)
    ExternVA{}      -> (a,b,c,d,e,f,g,h,x:i,j)
    Import{}        -> (a,b,c,d,e,f,g,h,i,x:j)


parseProg :: Parser [Decl]
 = noIndent decl `sepEndBy` many endLine

decl :: Parser Decl -- top level
 = svIndent parseDecl
  where
  parseDecl = choice
   [ Import <$> importDecl, extern
   , typeAlias, infixDecl, defaultDecl
   , typeClass, typeClassInst
   , try funBind, typeSigDecl]

  -- Note "renaming", "hiding", "as" and "to" are not reserved
  -- since import lists are independent from bindings
  importDecl = let
    require  = Require <$ reserved "require" <*> pModuleName
    open = let unMaybe = \case {Nothing->[] ; Just x -> x}
      in do
      openImport <- reserved "import"  *> pModuleName
      hides   <-optional (symbol "hiding" *> iden `sepBy2` symbol ",")
      renames <-
        let rename = (,) <$> iden <* symbol "to" <*> iden
        in optional (symbol "renaming"*>rename `sepBy2` symbol ",")
      pure $ case (unMaybe renames, unMaybe hides) of
        ([], []) -> Open openImport
        (renames, hides) -> ImportCustom openImport hides renames
    importAs = ImportAs <$> importDecl <* symbol "as" <*> pModuleName
    in do
      importDecl <- choice [require, open]
      (optional $ symbol "as" *> pModuleName) <&> \case
        Just as -> ImportAs importDecl as
        Nothing -> importDecl

  extern = choice
   [ Extern  <$reserved "extern"      <*> name<*reservedOp ":"<*>pType
   , ExternVA<$reserved "externVarArg"<*> name<*reservedOp ":"<*>pType]
  typeAlias :: Parser Decl
  typeAlias = let
    defOrFun pTy = try (tyFun (TypeExp <$> pTy)) <|> tyDef pTy
    tyFun pTy= TypeFun   <$> tyName <*> some tyVar<* symboln "=" <*> pTy
    tyDef pTy= TypeAlias <$> tyName               <* symboln "=" <*> pTy
    in choice
    [ reserved "type"   *> defOrFun pType
    , reserved "data"   *> defOrFun tyData
    , reserved "record" *> defOrFun tyRecord]

  infixDecl = let
    pInfix = choice
      [ reserved "infix"  $> AssocNone
      , reserved "infixr" $> AssocRight
      , reserved "infixl" $> AssocLeft]
    opNames = (\x->[x]) <$> symbolName --`sepBy` symbol ","
    in InfixDecl <$> pInfix <*> optional (lexeme L.decimal) <*> opNames
  fnName = name <|> parens symbolName

  -- TODO indentation for where
  pWhere        = reserved "where" *> scn
  typeClass     = reserved "class" $> TypeClass <*>
                  tyName <*> some (try tyVar) <* pWhere
                  <*> bracesn (some (decl <* scn))
  typeClassInst = 
    reserved "instance" $> TypeClassInst
    <*> tyName <*> tyName <* pWhere <*> bracesn (some (decl <* scn))

  -- Flexible type vars are possible in type signatures
  funBind = dbg "fnbind" $ FunBind <$> some match
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
  match = dbg "match" $ do 
    (Match <$> (name <|> parens symbolName) <*> many (lexeme pat)
      <|> InfixMatch <$> lexeme pat <*> infixName <*> many (lexeme pat))
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

pExp :: Parser PExp = dbg "pexp" $
  appOrSingle >>= \app ->
    optional (infixTrain app) >>= \case
      Nothing      -> pure app
      Just infixes -> pure infixes
  where
  appOrSingle = single >>= \fn -> choice
   [ App fn <$> some single
   , pure fn
   ]
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
  infixTrain lArg =
    let infixOp = qName infixName
    in  InfixTrain lArg <$> some ((,) <$> infixOp <*> appOrSingle)
  opSection = SectionR <$> qName infixName <*> pExp
  someName = dbg "someName" $ choice
    [ Con . UnQual <$> uIden
    , Var <$> qName lIden
    , Var <$> try (qName (parens symbolName)) ]
  lambda = Lambda <$ char '\\' <*> many pat <* symbol "->" <*> pExp
  lambdaCase = LambdaCase <$> (char '\\' <* reserved "case" *> many (alt <* scn))
  letIn = reserved "let" *> do
    ref <- ask -- reference indentation
    scn
    lvl <- L.indentLevel
    local (const lvl) $ dbg "letBinds" $ do -- save this indent
      binds <- BDecls <$> indentedItems ref lvl scn decl (reserved "in")
--    binds <- BDecls <$> decl `sepBy` symbol ";"
      reserved "in"
      p <- pExp
      pure (Let binds p)
  -- it's assumed later that there is at least one if alt
  multiIf = reserved "if" *> choice [normalIf , multiIf]
      where
      normalIf = do
        ifE   <- pExp
        thenE <- reserved "then" *> pExp
        elseE <- reserved "else" *> pExp
        pure (MultiIf [(ifE, thenE), (WildCard, elseE)])
      subIf = (,) <$ reservedOp "|" <*> pExp <* reservedOp "=" <*> pExp
      multiIf = do
        l <- L.indentLevel
        iB (pure $ L.IndentSome (Just l) (pure . MultiIf) subIf)

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
tyData :: Parser Type =
 let parseAlts alt = ((,) <$> tyName <*> alt) `sepBy` symboln "|"
     recordFields :: Parser [(Name, Type)] =
       let field = (,) <$> tyVar <* reservedOp ":" <*> pType
       in  lexemen field `sepBy` lexemen ","
 in choice
 [ TyRecord    <$> parseAlts (bracesn recordFields)
 , TyData      <$> try (parseAlts (many singleType))
 , TyInfixData <$> singleType <*> infixName <*> singleType
 ]

tyRecord = fail "use haskell style records for now pls"

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
