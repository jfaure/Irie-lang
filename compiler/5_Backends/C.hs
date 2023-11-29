{-# Language TemplateHaskell #-}
module C where
import Prim
import CoreSyn
import PrettyCore
import Externs
import Blaze.ByteString.Builder
import Blaze.ByteString.Builder.Char8
import qualified Data.ByteString.Lazy as BSL
import qualified BitSetMap as BSM
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as VU
import qualified Data.Text as T
import Data.Functor.Foldable
import Data.Int
import Control.Lens
import System.Process

-- ! Write emits code and precomputes lengths.
-- ! to serialize bounded things use: fromWrite $ writeWord8 x <> writeWord8 y <> writeByteString "hello"
-- This computes upper bound and does only one overflow check

data AsmType
 = CBits Int
 | CStruct (BSM.BitSetMap AsmType) -- Int total bits needed?
 | CSum    (Int , BSM.BitSetMap AsmType , Int) -- num alts , largest alt
data Value
 = Arg   { argName :: IName , vType ::  AsmType }
 | Local { locName :: IName , vType :: AsmType } -- in x86 = Reg | JmpCond | StackSlot
 | Anon  { vType :: AsmType } -- only valid in C where we don't explicitly allocate regs

data EmitCState = EmitCState
  { _argRegs :: V.Vector Value
  , _regDups :: VU.Vector Int
  }; makeLenses ''EmitCState
type MkX86M = StateT EmitCState IO

 -- ? Label , cast into sumtype
type CallingTy   = ([AsmType] , AsmType)
type CallingConv = (V.Vector Value , Value) -- for ASM to care about

-- TODO: must topologically sort
mintersperse a b = mconcat (intersperse a b)

mkCModule (dumpC , runC) moduleIName loadedMods moduleTT = do
  let outFile = "/tmp/runC.out"
      srcFile = "/tmp/Csrc.c"
      cModule = emitCModule moduleIName loadedMods moduleTT
      csrcTxt = toLazyByteString (mkHeader <> cModule)
  putStrLn @Text "> dump CSrc:"
  putStrLn csrcTxt
  BSL.writeFile srcFile csrcTxt
  when runC $ do
    putStrLn @Text "\n> Running C:"
    (clangOK , cout , cstderr) <- readProcessWithExitCode "gcc" [srcFile , "-o" <> outFile] ""
    case clangOK of
      ExitFailure _ -> putStrLn cout *> putStrLn cstderr
      ExitSuccess -> do
        (exitCode , asmStdout , asmStderr) <- readProcessWithExitCode outFile [] ""
        putStrLn asmStdout
        print exitCode

-- #define transmute(v,to) ((union {typeof(v) from; to to_;}{.from=v}).to_
mkHeader :: Builder
mkHeader = fromWriteList writeByteString
  [ "#include <stdint.h>\n"
  , "#include <stdio.h>\n"
  , "#include <stdlib.h>\n"
--, "#include <immintrin.h>\n"
--, "#define BOX(ty,b) ({ty *p = malloc(sizeof(ty)); *p = (b); p;})\n"
--, "#define FromPoly(ty,b) ({ union { TPoly in; ty out; } ret; ret.in  = (b); ret.out;})\n"
--, "#define ToPoly(ty,b)   ({ union { TPoly in; ty out; } ret; ret.out = (b); ret.in;})\n"
--, "#define CastStruct(t1,t2,b) ({ union { t1 in; t2 out; } ret; ret.in= (b); ret.out;})\n"
--, "typedef __m256 TPoly;\n\n"
  ]

emitCModule :: ModuleIName -> V.Vector LoadedMod -> V.Vector (LetMeta , Bind) -> Builder
emitCModule modIName loadedMods lets = let
--fnName lm = "f" <> show (unQName (letIName lm))
  fnName lm = (letIName lm) & \q -> case lookupBindName loadedMods modIName (unQName q) of
    Just hNm | modIName == modName q -> hNm
    _ -> error (show q)
  binds = lets <&> \(lm , (BindOK _ rhs)) -> emitFunction (toS $ fnName lm) (getCallingConv rhs) rhs
  in V.foldl (<>) mempty binds -- inefficient
--in mintersperse "\n" (V.toList binds) -- inefficient

-- v ASM must also allocate the registers according to calling conv
getCallingConv :: Expr -> ([AsmType] , AsmType)
getCallingConv (Core bindTerm ty) = let
  ccTy@(argTys , retTy) = case ty of
    TyGround [THTyCon (THArrow ars ret)] -> (tyToAsmTy <$> ars , tyToAsmTy ret)
    t -> (mempty , tyToAsmTy t)
  in ccTy

tyToAsmTy (TyGround [th]) = case th of
  THPrim (PrimInt n)         -> CBits n
  THPrim (PtrTo (PrimInt n)) -> CBits 64
--THTyCon tcon -> case tcon of
--  THProduct bsm -> tyToAsmTy <$> bsm & \prod -> CStruct (sizeOfProd prod , prod)
--  THTuple   bsm -> tyToAsmTy <$> bsm & \prod -> CStruct (sizeOfProd prod , BSM.fromList $ V.toList (V.indexed prod))
--  THSumTy   bsm -> tyToAsmTy <$> bsm & \prod -> let
--    maxSz = maximum (asmSizeOf <$> prod)
--    in SumTy (BSM.size prod , prod , maxSz)
  x -> error $ show x
tyToAsmTy t = error $ "asm: cannot codegen type: " <> toS (prettyTyRaw t)

--emitTypeDef i ty = let
--  in "typedef " <> emitType ty <> " T" <> fromString (show i) <> ";\n"

emitType :: _ -> Builder
emitType = \case
 CBits n | n <= 64 -> fromByteString "uint64_t"
-- CStruct fields -- (BSM.BitSetMap AsmType)
-- CSum alts --   (Int , BSM.BitSetMap AsmType , Int) -- num alts , largest alt

-- ↓ argRegs , dups , liveRegs , [stackSz]
-- ↑ allocate reg/mem
emitC :: TermF Builder -> Builder
emitC = \case
  -- vv TODO hardcoded, pass down env.
  -- each case branch resets the dupcounts; other AST nodes mutate dupcounts
  VBruijnF v -> "a0"
  VarF (VQBindIndex q) -> "fib"
  AppF f ars -> f <> "(" <> mintersperse " , " ars <> ")"
  LitF l -> emitLiteral l
  InstrAppF i args -> emitPrimInstr i args
  -- v elaborate
  CaseBF mkScrut _t alts Nothing | BSM.size alts == 2 , [ko , ok] <- V.toList (BSM.elems alts) ->
    "if (" <> mkScrut <> ")\n  " <> ok <> "\nelse\n  " <> ko
  ReturnF r -> "return " <> r <> ";"
  x -> error $ show (embed $ Question <$ x)

-- ret_ty fnName(arg1Ty arg1Nm , t2 n2) { .. }
-- TODO push down return statement!
emitFunction :: String -> CallingTy -> Expr -> Builder
emitFunction fnName (args , retTy) (Core term _) = let
  mkReturn = \case
    CaseB scrut t alts d -> CaseB scrut t (mkReturn <$> alts) (mkReturn <$> d)
    t -> Return t
  rhs = case term of
    BruijnAbs n dups body -> case compare (length args) n of -- TODO rm length
      EQ -> body
      GT -> error "pap"
      LT -> error $ "impossible: function has non-function type: " <> show fnName
  emitParam (i :: Int) t = emitType t <> " a" <> fromString (show i)
  in emitType retTy <> fromChar ' '
   <> fromString fnName <> fromChar '('
   <> mintersperse " , " (Prelude.imap emitParam args) -- TODO write foldM
   <> "){\n"
   <> cata emitC (mkReturn rhs)
   <> "\n}"

-- Primitives --
emitPrimInstr i = \case
  [a]   -> emitInstr i a
  [a,b] -> emitBinInstr i a b
  x -> error $ show i <> " applied to " <> show (length x) <> " args"

emitInstr i a = case i of
  PutNbr -> "printf(\"%d\\n\" , " <> a <> ")"
  Puts   -> "puts(" <> a <> ")"
  NumInstr (BitInstr Not)  -> "!(" <> a <> ")"

emitBinInstr i a b = let
  emitInfix str = a <> fromChar ' ' <> fromString str <> fromChar ' ' <> b
  in parens $ emitInfix $ case i of
  NumInstr j -> case j of
    IntInstr ii -> case ii of { Add -> "+" ; Sub -> "-" ; Mul -> "*" ; SDiv-> "/" ; SRem-> "%" }
    PredInstr pi -> case pi of { LECmp -> "<=" ; GECmp -> ">=" ; LTCmp -> "<"
                               ; GTCmp -> ">" ; EQCmp -> "==" ; NEQCmp-> "!=" ; AND->"&&" ; OR->"||" }
    BitInstr bi -> case bi of { Xor -> "^" ; And -> "&" ; Or  -> "|" ; ShL -> "<<" ; ShR -> ">>" }
    x -> error $ show x

parens p = fromChar '(' <> p <> fromChar ')'

emitLiteral = \case
  Char c  -> fromString $ show c
  Fin n i -> case n of
    8  -> {-"(uint8_t)"  <> -} fromString (show i)
    16 -> {-"(uint16_t)" <> -} fromString (show i)
    32 -> {-"(uint32_t)" <> -} fromString (show i)
    64 -> {-"(uint64_t)" <> -} fromString (show i)
    128-> "(uint128_t)" <> fromString (show i)
    _  -> error $ show n
  String s -> fromChar '"' <> fromString s <> fromChar '"'
  LitArray  l -> fromChar '{' <> mconcat (intersperse (fromChar ',') (emitLiteral <$> l)) <> "};"

emitPrimType :: PrimType -> Write
emitPrimType (PtrTo p) = emitPrimType p <> writeChar '*'
emitPrimType p = writeByteString $ case p of
  PrimInt 8  -> "int8_t"
  PrimInt 32 -> "int32_t"
  PrimInt 64 -> "int64_t"
  PrimNat 8  -> "uint8_t"
  PrimNat 32 -> "uint32_t"
  PrimNat 64 -> "uint64_t"
  x -> error ("C-emitprimtype: " <> show x)
