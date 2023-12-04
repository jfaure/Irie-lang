{-# Language TemplateHaskell , QuasiQuotes #-}
module C where
import Prim
import CoreSyn
import PrettyCore
import Externs
import Builtins(typeOfLit)
import MyString
import Blaze.ByteString.Builder
import Blaze.ByteString.Builder.Char8
import qualified Data.ByteString as BS
import qualified BitSetMap as BSM
import qualified Data.ByteString.Internal as BS
import qualified Data.ByteString.Lazy as BSL
import qualified Data.ByteString.Lazy.Internal as BSL
import qualified BitSetMap as BSM
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as VU
import qualified Data.Text as T
import Text.RawString.QQ
import Data.Functor.Foldable
import Data.Int
import Control.Lens
import System.Process
import System.IO.Unsafe

getIName :: V.Vector LoadedMod -> QName -> ByteString
getIName loadedMods q = case lookupIName loadedMods (modName q) (unQName q) of
  Just hNm -> encodeUtf8 hNm
  got -> error $ show got <> ": " <> show q

getFieldName loadedMods q = if modName q == 0
  then "_" <> show (unQName q) -- tuples are qnamed in the builtin module '0'
  else getIName loadedMods q

-- Note. see C disassembly = objdump -d -Mintel --visualize-jumps=color --disassembler-color=on --disassemble=fName
-- recursions: Tail , Linear , Binary/Multiple , Mutual , Nested , Tree , Generative , Course-of-Values
------------------------------
-- Tycon Operational semantics
------------------------------
-- * label/field -> asmIdx = Sort on: size , QName , IName
-- * Prod:
-- * Labels: Do nothing at Label, only at cast, so fullest context available
--     Label = tag struct (separate fixed size struct describing label tree). 2 labels => mk arrays
--     * RecLabel (! multiple μs ; exponentially different tree structures)
--   # Lab-cast: (re)alloc label, maybe shuffle tag idxs & ptrHeader
--   # Lab-open: Era args , free node
--   # Lab-dup:
--   # Lab-merge: (A (B d)) : [0 [2 Int] | 1]
-- ? free: After last use | Era branch not taken | ? bounds on lifetimes
-- * paps => specialise: All fnPtrs are given extra regs (64bit fnptr , u64 & u256 data) ; OF => heap-alloc
-- ? branch bruijn containments (so last use is evident , and branch ordering flexible)

data SumType -- Unused
 = SumNat   -- simplest form of labels with no data
 | SumPeano -- recursive no-data labels can be represented as Nats
 | SumEnum  -- no-rec labelled datas
 | SumList  -- rec branch factor 1
 | SumTree  -- multiple branches (also multiple μ knots)
 | SumMany [SumType] -- multiple types of sumtype
-- recursive Tree data Automata; enumerate data modulo N (constructors)
-- ; build NFA transition table. Spawn Arrays
-- multi-μ: µb.[Node {A , µc.[Nil | Cons {b , c}]}]

type AsmIdx = Int -- QName -> [0..] flattened name in context
type AsmType = TyHead

-- * Every TBound gets its own typedef
-- * Every Struct that passes through a function gets its own typedef
-- BasicTypes are 1:1 to Terms, so constructed/deconstructed in lockstep with Core operations
-- so we can track types of arg/ret ↓↑ during codegen
data BasicTy
  = BPrim PrimType
  | BBound ByteString -- point to typedef
  | BStruct (BSM.BitSetMap BasicTy)
  | BEnum Int -- trivial sumtype. (incl. Peanos?)
--  | BNewType Int BasicTy -- sumtype of 1 alt, the label is implicit
-- Note. if sumtype has only 1 tag, tag is removed.
  | BSum Int{-nTags-} (BSM.BitSetMap BasicTy) Int {-maxSz-} -- if larger than reg_call, malloc the data
  | BVoid
  deriving Show
--  | BTree
--  | BList

-- incls register(s) in ASM
data Value = VArg IName | VLocal IName | VLens Value [ByteString] | Tag Int Value deriving Show

-- pass down typedef for structure types
tyToBasicTy :: TyHead -> BasicTy
tyToBasicTy = \case
  THPrim p -> BPrim p
  THTyCon tcon -> case tcon of
    THProduct bsm -> BStruct (bsm <&> \(TyGround [t]) -> tyToBasicTy t)
    THTuple   tys -> BStruct (BSM.fromVec $ V.imap (\i (TyGround [t]) -> (qName2Key (mkQName 0 i) , tyToBasicTy t)) tys)
    THSumTy   bsm -> let
      collect :: Int -> (Int , Type) -> Int
      collect (maxSz) (_qNm , ty) = (max maxSz (sizeOf ty))
      maxSz = BSM.foldlWithKey collect 0 bsm
      tagCount = BSM.size bsm -- bits = intLog2 tagCount
      in if
        | maxSz    == 0 -> BEnum tagCount --  (PrimNat bits)
        | tagCount == 1 , [(tag , TyGround [ty])] <- BSM.toList bsm ->
          BSum tagCount (BSM.singleton tag (tyToBasicTy ty)) maxSz
        | True -> _BSum
--  THArrow{} -> "TArrow"
    t -> traceTy (TyGround [THTyCon t]) (error "")
  THBi _ (TyGround [ty]) -> tyToBasicTy ty
--THBound i -> "TBound"
  t -> traceTy (TyGround [t]) (error "")

serialiseBasicTy :: V.Vector LoadedMod -> BasicTy -> (BasicTy , ByteString)
serialiseBasicTy loadedMods t = let
  convStep = \case
    BPrim p -> NBStr (toByteString $ fromWrite $ emitPrimType p)
    BBound td -> NBStr td -- point to typedef
    BStruct bs -> let
      emitField (q , fieldType) = let
        in [Right fieldType , Left (" " <> getFieldName loadedMods (QName q) <> "; ")]
      in NChunks (Left "struct { " : concatMap emitField (BSM.toList bs) ++ [Left " }"])
    BEnum tagCount -> NBStr $ toByteString $ fromWrite $ emitPrimType (PrimNat (intLog2 tagCount))
    BSum 1 alts sz | [(tag , ty)] <- BSM.toList alts -> NSkip ty
--  BVoid -> NDone
--  BNewType ->
  in (t , snd $ unfoldrChunks convStep t)

-- size in bytes of a type
sizeOf :: Type -> Int
sizeOf = \case
  TyGround [t] -> case t of
    THPrim p -> sizeOfPrim p
    THTyCon tycon -> case tycon of
      THTuple t -> if null t then 0 else sum (sizeOf <$> t)
  _ -> _

type CCTy = (BasicTy , ByteString)
type CallingConv = ([CCTy] , CCTy)

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
    putStrLn @Text ("\n> Compiling and running C: " <> toS srcFile <> " -> " <> toS outFile <> ":")
    (clangOK , cout , cstderr) <- readProcessWithExitCode "gcc" [srcFile , "-march=haswell" , "-o" <> outFile] ""
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
--, "#include <immintrin.h>\n" Massively slows down compile times..
  , "typedef uint64_t u64; " , "typedef uint32_t u32; " , "typedef uint8_t u8; " , "typedef uint8_t u1;\n"
  , "typedef int64_t i64; "  , "typedef int32_t i32; "  , "typedef int8_t i8; "  , "typedef int8_t i1;\n"
  , "#define CastStruct(GOT,WANT,b) ({ union { GOT got; WANT want; } ret; ret.got = (b); ret.want;})\n"
  , "typedef struct { u64 r; u64 rx; } Ret128;\n" -- c-call convention allows in-reg return of 2 u64s
  , "typedef Ret128 TArrow; typedef Ret128 TBound;\n"
  , "// Custom Defs //\n\n"
--, "#define BOX(ty,b) ({ty *p = malloc(sizeof(ty)); *p = (b); p;})\n"
--, "#define CastStruct(t1,t2,b) ({ union { t1 in; t2 out; } ret; ret.in= (b); ret.out;})\n"
  ]

emitCModule :: ModuleIName -> V.Vector LoadedMod -> V.Vector (LetMeta , Bind) -> Builder
emitCModule modIName loadedMods lets = let
  fnName lm = (letIName lm) & \q -> case lookupIName loadedMods (modName q) (unQName q) of
    Just hNm | modIName == modName q -> hNm
    got -> error $ show got <> ": " <> show q
  fnToStr (Right (fnDecl , fnBody)) = [fnDecl , " {\n  " , fnBody , "\n}\n"]
  fnToStr (Left  (fnDecl , fnBody)) = [fnDecl , " " , fnBody , ";\n\n"]
  binds = lets <&> \(lm , (BindOK _ rhs)) -> fnToStr $
    emitFunction loadedMods (encodeUtf8 (fnName lm)) (getCallingConv loadedMods rhs) rhs
  in fromWriteList writeByteString (concat $ V.toList binds)

-- v ASM must also allocate the registers according to calling conv
getCallingConv :: V.Vector LoadedMod -> Expr -> CallingConv
getCallingConv loadedMods (Core bindTerm ty) = let
  mkBasicTy = serialiseBasicTy loadedMods . tyToBasicTy
  (argTys , retTy) = case ty of
    TyGround [THTyCon (THArrow ars ret)] -> (tyToAsmTy <$> ars , tyToAsmTy ret)
    TyGround [THBi _ (TyGround [THTyCon (THArrow ars ret)])]  -> (tyToAsmTy <$> ars , tyToAsmTy ret)
    -- TODO incomplete
    t -> (mempty , tyToAsmTy t)
  in (mkBasicTy <$> argTys , mkBasicTy retTy)

tyToAsmTy (TyGround [th]) = th
tyToAsmTy t = error $ "asm: cannot codegen type: " <> toS (prettyTyRaw t)

-- ↓ next term , dups , retLoc (esp. ret typdef)
-- ↑ dependencies, literals, fns
-- ↓↑ state for the unfolding
data Env = Env { retVal :: BasicTy , argEnv :: V.Vector (Value , BasicTy) } deriving Show
data CSeed = Up BasicTy | Dwn (Env , Term) deriving Show
termToCU :: V.Vector LoadedMod -> CSeed -> NextChunk CSeed
termToCU loadedMods (Up ty) = NEnd (Up ty)
termToCU loadedMods (Dwn (env , term)) = let
  idSeed t = Dwn (env , t)
  in case term of
  Return cast f  -> NEnclose ("return " <> cast) (idSeed f) ";"
  Lit l -> NStr (emitLiteral l) (Up $ tyToBasicTy (typeOfLit l))
  VBruijn v -> argEnv env V.! v & \(val , ty) -> let
    showValue = \case
      VArg i   -> ("a" <> show i)
      VLocal i -> ("l" <> show i)
      VLens v fields -> BS.intercalate "._" (showValue v : fields)
    in NStr (showValue val) (Up ty)
  Var (VQBindIndex q) -> case lookupBindName loadedMods (modName q) (unQName q) of
    Just hNm -> NBStr (encodeUtf8 hNm) -- ! Get the calling conv
    got -> error $ show got <> ": " <> show q
  Cast cast x -> case cast of
    CastZext n -> let castStr = writeToByteString $ writeChar '(' <> emitPrimType (PrimNat n) <> writeChar ')'
      in NChunks [Left castStr , Right (idSeed x) , Right (Up (BPrim (PrimNat n)))]
    cast -> error $ show cast
--  CastProduct{}
  App f args -> case f of
    Instr i -> if -- This automatically returns the Up of the last operand, fine for almost all instructions
      | infixTxt <- emitInfixInstrText i , infixTxt /= "?" , [lOp , rOp] <- args ->
        NChunks [Left "(" , Right (idSeed lOp) , Left (" " <> infixTxt <> " ") , Right (idSeed rOp) , Left ")"]
      | [arg] <- args -> let mkFunction fnName arg = NEnclose fnName (idSeed arg) ")"
        in case i of
        PutNbr -> mkFunction "printf(\"%d\\n\" , " arg -- TODO different int types
        Puts   -> mkFunction "puts(" arg
        NumInstr (BitInstr Not) -> mkFunction "!(" arg
        _ -> _
      | otherwise -> error $ "panic: bad instr: " <> show i
    _ -> let l = (Right (idSeed f) : Left "(" : intersperse (Left " , ") (Right . idSeed <$> args)) ++ [Left ")"]
      in NChunks l

  -- * Pass down type for prods and sums; sub-products split each field into a retLoc
  Prod  bsm  -> let
    mkField (q , fieldVal) = getFieldName loadedMods (QName q) & \hNm ->
      [Left ("." <> hNm <> "=") , Right (idSeed fieldVal) , Left ", "]
    in NChunks (Left "{ " : (concatMap mkField (BSM.toList bsm)) ++ [Left "}"])
  -- The cast is an artefact of inference, TODO have infer. remove it / cast after extraction
  TTLens rawObj fields LensGet -> let
    mkAccess f = "." <> getFieldName loadedMods (QName f)
    in case rawObj of
    Cast (CastProduct 1 [(idx , leafCast)]) obj -> -- TODO leafCast
      NEndStr (idSeed obj) (mconcat $ mkAccess <$> fields)
    obj ->
      NEndStr (idSeed obj) (mconcat $ mkAccess <$> fields)

  Label l args -> error "label" -- Since wasn't caught by a cast, does nothing (identity label)

-- lit-case => (int [2]){ 5 , 0 }[a0];
--CaseB scrut _t alts Nothing | BSM.size alts == 2 , [(_koq , ko) , (_okq ,ok)] <- BSM.toList alts ->
--  NStr "if (" (idSeed UnfoldList [scrut , UnfoldStr ") " , ok , UnfoldStr "\n  else " , ko] "")

  -- TODO default , LitArray , altCasts
  -- scrut = | Enum | Tag
  -- ! Must know scrut Type => To name it (scrut.tag , scrut.data) & interpret tag
  CaseB scrut scrutTy alts d -> let -- BSM sorts on QName already, so can imap to get asmidxs TODO?
    last = BSM.size alts - 1
    mkAlt :: Int -> BasicTy -> Int -> (Int , Term) -> [Either ByteString CSeed]
    mkAlt scrutName (BSum nTags altTys maxSz) asmIdx (_qNm , term) = let
      altTerm = case term of
        BruijnAbs n _ rhs -> rhs -- TODO hack, need to add locals to env
        t -> t
      caseTxt = if asmIdx == last && isNothing d then "default: " else "case " <> show asmIdx <> ": "
      breakTxt = case altTerm of { Return{} -> "\n  "  ; _ -> "\n  " } -- break? not needed
      scrutLenses = V.imap (\i ty -> (VLens (VLocal scrutName) [show i] , ty)) (BSM.elems altTys)
      -- ! lift alt-fns OR need to remap deBruijns so the first n point to data in this label
      altEnv = Env (retVal env) (scrutLenses <> argEnv env)
      in [Left caseTxt , Right (Dwn (altEnv , altTerm)) , Left breakTxt]
    altList scrutName ty = (concat $ Prelude.imap (mkAlt scrutName ty) (BSM.toList alts))

   -- Left ("({ " <> snd (serialiseBasicTy loadedMods scrutTy) <> " scrut = ")
    namedScrut scrutName scrutTy = NChunks
      $ Left "switch (" : Right (idSeed scrut) : Left ") {\n  " : altList scrutName scrutTy
      ++ [Left "}"]

    anonScrut scrutTy readTag = NChunks
      $ Left "switch ("
      : Right (idSeed scrut)
      : Left (if readTag then ".tag) {\n  " else ") {\n  ")
      : altList 0 scrutTy
      ++ [Left "})"]
    in case scrut of -- enums don't need a name, but all other scruts do
      VBruijn i -> argEnv env V.! i & \(_value , ty) -> case ty of
        BSum nTags tys maxSz -> anonScrut ty False
        ty -> anonScrut ty False
      -- TODO enum scruts don't need a name
      _ -> _ -- anonScrut (d_ "warning: i32 assumed" $ BPrim (PrimInt 32)) True -- TODO bind the scrut onto a caseAlts

  X86Intrinsic "_mm256_undefined_si256" -> NBStr "_mm256_undefined_si256()"
  X86Intrinsic txt -> NBStr (encodeUtf8 txt)
  x -> error $ show x

--termToC :: V.Vector LoadedMod -> Term -> (Term , ByteString)
termToC loadedMods term = unfoldrChunks (termToCU loadedMods) term

-- [typedefs] , ret_ty fnName(arg1Ty arg1Nm , t2 n2) { .. }
emitFunction :: V.Vector LoadedMod -> ByteString -> CallingConv -> Expr
  -> Either (ByteString , ByteString) (ByteString , ByteString)
emitFunction loadedMods fnName (argT , retT) (Core term _) = let
  nArgs = length argT
  (retBTy  , rawRetStr) = retT
  (argBTys , rawArgStrs) = unzip argT

  -- Use typedefs rather than raw types for structs. (No choice for structs passing through calling convs)
  needsTypeDef = \case { BStruct{} -> True ; _ -> False }
  maybeTypedef idx (bty , rawTyStr) = if needsTypeDef bty
    then let td = fnName <> if idx < 0 then "_RT" else "_AT" <> show idx
      in (td , Just ("typedef " <> rawTyStr <> " " <> td <> ";\n"))
    else (rawTyStr , Nothing)
  (retTyStr : argTyStrs , maybeTypedefStrs) = unzip $ zipWith maybeTypedef (-1 : [nArgs-1 , nArgs-2 .. 0]) (retT : argT)
  typedefStrs = mconcat (catMaybes maybeTypedefStrs)

  rhs = case term of
    BruijnAbs n dups body -> case compare nArgs n of -- TODO rm length
      EQ -> body
      GT -> error "pap"
      LT -> error $ "impossible: function has non-function type: " <> show fnName
    BruijnAbsTyped{} -> _
    x -> x

  mkReturn = \case
    CaseB scrut t alts d -> CaseB scrut t (mkReturn <$> alts) (mkReturn <$> d)
    BruijnAbs n d rhs -> BruijnAbs n d (mkReturn rhs)
    t -> Return (if needsTypeDef retBTy then "(" <> retTyStr <> ")" else "") t -- eg. "(retTy){.f=3}"

  emitParam (i :: Int) tystr = tystr <> " a" <> show i
  fnDecl = typedefStrs <> retTyStr <> " " <> fnName <> "("
    <> BS.intercalate " , " (zipWith emitParam [nArgs - 1 , nArgs - 2 .. 0] argTyStrs) <> ")"

  argValues = zipWith (\i ty -> (VArg i , ty)) [nArgs - 1 , nArgs - 2 .. 0] argBTys
  mkRhs rhs = snd $ termToC loadedMods (Dwn (Env retBTy (V.fromList argValues) , rhs))
  in if nArgs == 0 && fnName /= "main"
    then Left (typedefStrs <> retTyStr <> " const " <> fnName <> " =" , mkRhs rhs)
    else Right (fnDecl , mkRhs (mkReturn rhs))

-- returns "?" if doesn't know the textual representation
emitInfixInstrText = \case
  NumInstr j -> case j of
    IntInstr ii -> case ii of { Add -> "+" ; Sub -> "-" ; Mul -> "*" ; SDiv-> "/" ; SRem-> "%" ; _ -> error "todo" }
    PredInstr pi -> case pi of { LECmp -> "<=" ; GECmp -> ">=" ; LTCmp -> "<"
                               ; GTCmp -> ">" ; EQCmp -> "==" ; NEQCmp-> "!=" ; AND->"&&" ; OR->"||" }
    BitInstr bi -> case bi of { Xor -> "^" ; And -> "&" ; Or  -> "|" ; ShL -> "<<" ; ShR -> ">>" ; _ -> error "todo" }
    _ -> "?" -- convention bad infix
  _ -> "?" -- convention bad infix

emitLiteral :: Literal -> ByteString
emitLiteral = \case
  Char c  -> BS.singleton (BS.c2w c)
  Fin _n i -> let -- cast = "(" <> emitPrimType (PrimNat n) <> ")"
    in {-cast <>-} show i -- No need to cast literals, C knows their types
  String s -> show s -- fromChar '"' <> fromString s <> fromChar '"'
  LitArray  l -> "{" <> mconcat (intersperse "," (emitLiteral <$> l)) <> "}"
  l -> error $ show l

emitPrimType :: PrimType -> Write
emitPrimType (PtrTo p) = emitPrimType p <> writeChar '*'
emitPrimType p = writeByteString $ case p of
  PrimInt n  -> if
    | n <= 1  -> "i1"
    | n <= 8  -> "i8"
    | n <= 32 -> "i32"
    | n <= 64 -> "i64"
    | True -> _
  PrimNat n -> if
    | n <= 1  -> "u1"
    | n <= 8  -> "u8"
    | n <= 32 -> "u32"
    | n <= 64 -> "u64"
    | True -> _
  X86Vec 128 -> "__m128i"
  X86Vec 256 -> "__m256i"
  x -> error ("C-emitprimtype: " <> show x)

-- TODO alignment requirements
sizeOfPrim = let
  bitSize n = div n 8
  in \case
  PrimInt n -> bitSize n
  PrimNat n -> bitSize n
  _ -> _
