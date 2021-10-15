module C where
import Prim
import SSA
import Blaze.ByteString.Builder
import Blaze.ByteString.Builder.Char8
import qualified Data.Vector as V
import qualified Data.Text as T

--toLazyByteString

mkC ssaMod = toLazyByteString $
     "#include <stdint.h>\n"
  <> "#include <stdio.h>\n"
  <> "typedef struct { uint64_t ; void *p } TPoly;"
  <> "\n"
  <> mconcat (reverse $ V.toList $ V.imap emitTypeDef (typeDefs ssaMod))
  <> "\n"
  <> mintersperse "\n\n" (emitFunction ssaMod <$> (V.toList (locals ssaMod)))

emitTypeDef i ty = let
  in "typedef " <> emitType' True ty <> " T" <> fromString (show i) <> ";\n"
wrap a b c = a <> c <> b
brackets = wrap (fromChar '{') (fromChar '}')
mintersperse a b = mconcat (intersperse a b)

emitType = emitType' False
emitType' emitDef t = case t of
  TRec i  -> "struct T" <> fromString (show i) <> "*"
  TPoly   -> "void*"
  TPrim p -> emitPrimType p
  TStruct nm ts -> if emitDef
    then let
      fields = V.toList $ V.imap (\i t -> emitType t <> " f" <> fromString (show i) <> ";") ts
      in "struct " <> "T" <> fromString (show nm) <> "{ " <> (mconcat (intersperse " " fields)) <> "}"
    else "T" <> fromString (show nm)
  TSum nm ts -> let
--  fieldSize = fromString "sizeof (" <> emitType (ts V.! i) <> fromChar ')'
--  in fromString "struct { uint32_t f0 ; char f1[" <> fieldSize <> fromString "];}"
    fields = mintersperse "; " (V.toList $ V.imap (\i t -> emitType t <> fromString (" b" ++ show i)) ts) <> ";"
    in if emitDef
      then "struct " <> "T" <> fromString (show nm) <> "{ uint32_t f0 ; union {" <> fields <> "} f1;}"
      else "T" <> fromString (show nm)
--TypeDef i -> "T" <> fromString (show i)
  x -> error $ show x

emitFunction :: Module -> Function -> Builder
emitFunction ssaMod (Function fnDecl body) = let
  emitParam (i :: Int) t = emitType t <> "  a" <> fromString (show i)
  in
  emitType (retTy fnDecl) <> fromChar ' '
   <> fromString (T.unpack $ name fnDecl) <> fromChar '('
   <> (mconcat $ intersperse (fromChar ',') (zipWith emitParam [0..] (args fnDecl)))
   <> "){\n"
   <> emitBody ssaMod body
   <> "}"

emitBody :: Module -> Expr -> Builder
emitBody ssaMod = let
  emitBody' = emitBody ssaMod
  emitCallable = \case
--  LocalFn i -> let
--    decl = fnDecl (locals ssaMod V.! i)
--    in "((" <> emitType (retTy decl) <> " (*)(" <> (mconcat $ intersperse "," $ emitType <$> args decl) <> "))"
--      <> fromString (T.unpack $ name $ fnDecl $ locals ssaMod V.! i) <> ")"
    LocalFn i -> fromString (T.unpack $ name $ fnDecl $ locals ssaMod V.! i)
    Prim p -> _ -- instr wrapper error $ show x
  in \case
  Arg i    -> fromString $ 'a' : show i
  Local i  -> fromString $ 'l' : show i
  Extern i -> _
  LitE l   -> emitLiteral ssaMod l

  Call c ops -> let
    emitCall f argList = f <> "(" <> mconcat (intersperse "," argList) <> ")"
    in case c of
    Prim i  -> emitPrimInstr ssaMod i ops
    LocalFn i -> let
      decl = fnDecl (locals ssaMod V.! i)
      castArg t op@(Load{}) = emitBody' op -- don't need to cast if already the right type
      castArg t op = case t of
        TSum{}    -> "(" <> emitType t <> ")" <> emitBody' op
        TStruct{} -> "(" <> emitType t <> ")" <> emitBody' op
        x      -> emitBody' op
      in emitCall (emitCallable c) (zipWith castArg (args decl) ops)
    c -> emitCall (emitCallable c) (emitBody' <$> ops)
  Load  t (SSA.Gep t' i e) -> emitBody' e <> "[" <> fromString (show i) <> "]"
  Load t e      -> emitBody' e <> "[0]" -- "*(" <> emitBody' e <> ")"
  Index t i e   -> emitBody' e <> "->f" <> fromString (show i)
  Extract t i e -> emitBody' e <> ".f" <> fromString (show i)
  Gep t i e     -> "(&" <> emitBody' (Index t i e) <> ")"
  BitCast t e   -> "((" <> emitType t <> "*)" <> emitBody' e <> ")"
  UnUnion tag branchTy val -> emitBody' val <> ".b" <> fromString (show tag)
    -- fromChar '(' <> fromString (show i) <> " + "<> emitBody' e <> fromChar ')'
  Ret e -> "return " <> emitBody' e <> ";"
  SumData _ tag val -> "{" <> emitBody' tag <> " , " <> emitBody' val <> "}"
  Switch scrut brs d -> let
    emitBranch (const , val) = "case " <> fromString (show const) <> ":\n"
      <> emitBody' val
      <> "; break;\n"
    emitBranches = mconcat $ emitBranch <$> brs
    emitDefault = case d of { Void -> mempty ; Ret (Void) -> mempty ; x -> "default:\n" <> emitBody' x }
    in "switch (" <> emitBody' scrut <> ") {\n" <> emitBranches <> emitDefault <> "}"
--Void -> fromString "void" -- mempty
--Struct t vals -> "(" <> emitType' True t <> "){ " <> mintersperse "," (emitBody' <$> V.toList vals) <> " }"
  Struct t vals -> "{ " <> mintersperse "," (emitBody' <$> V.toList vals) <> " }"
  x -> error $ show x

emitPrimInstr ssaMod i args = case args of
  [a]     -> emitInstr ssaMod i a
  [a,b]   -> emitBinInstr ssaMod i a b
  [a,b,c] -> emitTriInstr ssaMod i a b c
  x -> error $ show i

emitTriInstr ssaMod i a b c = let
  emitBody' = emitBody ssaMod
  in case i of
  IfThenE -> "if (" <> emitBody' a <> ")\n  "
    <> emitBody' b <> "\nelse\n  " <> emitBody' c

emitInstr ssaMod i a = let
  emitBody' = emitBody ssaMod
  in case i of
  PutNbr -> "printf(\"%d\\n\" , " <> emitBody' a <> ")"
  Puts   -> "puts(" <> emitBody' a <> ")"
  NumInstr (BitInstr Not)  -> "!(" <> emitBody' a <> ")"

emitBinInstr ssaMod i a b = let
  emitInfix str = emitBody ssaMod a <> fromChar ' ' <> fromString str <> fromChar ' ' <> emitBody ssaMod b
  in parens $ case i of
  NumInstr j -> case j of
    IntInstr Add -> emitInfix "+"
    IntInstr Sub -> emitInfix "-"
    IntInstr Mul -> emitInfix "*"
    IntInstr SDiv-> emitInfix "/"
    IntInstr SRem-> emitInfix "%"

    PredInstr LECmp -> emitInfix "<="
    PredInstr GECmp -> emitInfix ">="
    PredInstr LTCmp -> emitInfix "<"
    PredInstr GTCmp -> emitInfix ">"
    PredInstr EQCmp -> emitInfix "=="
    PredInstr NEQCmp-> emitInfix "!="

    BitInstr Xor -> emitInfix "^"
    BitInstr And -> emitInfix "&"
    BitInstr Or  -> emitInfix "|"
    BitInstr ShL -> emitInfix "<<"
    BitInstr ShR -> emitInfix ">>"

parens p = fromChar '(' <> p <> fromChar ')'

emitLiteral ssaMod = \case
  Char c  -> fromString $ show c
  Int i   -> fromString $ show i
  Fin n i -> case n of
    8  -> "(uint8_t)"   <> fromString (show i)
    16 -> "(uint16_t)"  <> fromString (show i)
    32 -> "(uint32_t)"  <> fromString (show i)
    64 -> "(uint64_t)"  <> fromString (show i)
    128-> "(uint128_t)" <> fromString (show i)
  String s -> fromString s <> "\n"
  Array  l -> fromChar '{' <> mconcat (intersperse (fromChar ',') (emitLiteral ssaMod <$> l)) <> "};"

emitPrimType = \case
  PrimInt 8  -> "int8_t"
  PrimInt 32 -> "int32_t"
  PrimInt 64 -> "int64_t"
  PrimNat 8  -> "uint8_t"
  PrimNat 32 -> "uint32_t"
  PrimNat 64 -> "uint64_t"
