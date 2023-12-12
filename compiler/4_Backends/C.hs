{-# Language TemplateHaskell , QuasiQuotes #-}
module C where
import Prim
import CoreSyn
import Caster
import PrettyCore
import Externs
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

getRawIName :: V.Vector LoadedMod -> QName -> ByteString
getRawIName loadedMods q = case lookupIName loadedMods (modName q) (unQName q) of
  Just hNm -> encodeUtf8 hNm
  got -> error $ show got <> ": " <> show q

getIName loadedMods q = if modName q == 0
  then "_" <> show (unQName q) -- tuples are qnamed in the builtin module '0'
  else getRawIName loadedMods q

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

-- incls register(s) in ASM
data Value = VArg IName | VLocal IName | VLens Value [ByteString] | VTag Int Value | VVoid deriving Show

-- C fnptr typedefs are tragically idiotic, eg: "typedef retT ALIAS(aT0 , ...)"
-- ie. Have to embed the alias inside the type it is aliasing.
-- This forces us to handle the name here
-- TODO pass down field names for fnptr record fields
serialiseBasicTy :: V.Vector LoadedMod -> Maybe ByteString -> BasicType -> (BasicType , ByteString)
serialiseBasicTy loadedMods tyName bTy = let
  tagCountToTagType = BPrim . PrimNat . intLog2
  convStep = \case
    BPrim p -> NBStr (toByteString $ fromWrite $ emitPrimType p)
    BBound td -> NBStr "TBound" -- (show td) -- point to typedef
    BArrow ars ret -> NChunks $ (Left "(" : Right ret : Left " (*)(" : intersperse (Left " , ") (Right <$> ars)) ++ [Left "))"]
    BStruct bs -> let
      emitField (q , fieldType) = let
        in [Right fieldType , Left (" " <> getIName loadedMods (QName q) <> "; ")]
      in case BSM.toList bs of
        [(q , f)] -> NStr ("ImplF(" <> getIName loadedMods (QName q) <> ")") f
        fields    -> NChunks (Left "struct { " : concatMap emitField fields ++ [Left "}"])
    BEnum tagCount -> NSkip (tagCountToTagType tagCount)
    BSum 1 alts sz | [(tag , ty)] <- BSM.toList alts -> NStr ("ImplL(" <> getIName loadedMods (QName tag) <> ") ") ty
    BSum n alts sz -> let
      fields = BSM.toList alts <&> \(tag , subTy) ->
        [Right subTy , Left (" " <> getIName loadedMods (QName tag) <> "; ")]
      in NChunks $ Left "TSum(" : Right (tagCountToTagType n) : Left ") " : concat fields ++ [Left "} datum; } "]

  in case bTy of
    BArrow ars retT -> (bTy ,) $ snd (unfoldrChunks convStep retT)
      <> maybe "(*)" (\t -> "(*" <> t <> ")") tyName
      <> "(" <> BS.intercalate " , " (snd . unfoldrChunks convStep <$> ars) <> ")"
    _ -> (bTy , snd (unfoldrChunks convStep bTy) <> maybe "" (" " <>) tyName)

type CCTy = (BasicType , ByteString)
type CallingConv = ([CCTy] , CCTy)
newtype Typedef = Typedef { unTypedef :: ByteString }

-- TODO: must topologically sort
mintersperse a b = mconcat (intersperse a b)

mkCModule (dumpC , runC , requestOutFile) moduleIName loadedMods moduleTT depPerm = do
  let outFile = fromMaybe "/tmp/runC.out" requestOutFile
      srcFile = "/tmp/Csrc.c"
      cModule = emitCModule moduleIName loadedMods moduleTT depPerm
      csrcTxt = toLazyByteString (mkHeader <> cModule)
  when dumpC $ putStrLn @Text "> dump CSrc:" *> putStrLn csrcTxt
  BSL.writeFile srcFile csrcTxt

  putStrLn @Text ("\n> Compiling C: " <> toS srcFile <> " -> " <> toS outFile <> ":")
  (clangOK , cout , cstderr) <- readProcessWithExitCode "gcc" [srcFile , "-march=haswell" , "-o" <> outFile] ""

  when runC do
    putStrLn @Text "\n> Running C: "
    case clangOK of
      ExitFailure _ -> putStrLn cout *> putStrLn cstderr
      ExitSuccess -> do
        (exitCode , asmStdout , asmStderr) <- readProcessWithExitCode outFile [] ""
        when runC $ putStrLn asmStdout *> print exitCode

mkHeader :: Builder
mkHeader = fromWriteList writeByteString
  [ "#include <stdint.h>\n"
  , "#include <stdio.h>\n"
  , "#include <stdlib.h>\n"
--, "#include <immintrin.h>\n" Massively slows down compile times..
  , "typedef uint64_t u64; " , "typedef uint32_t u32; " , "typedef uint8_t u8; " , "typedef uint8_t u1;\n"
  , "typedef int64_t i64; "  , "typedef int32_t i32; "  , "typedef int8_t i8; "  , "typedef int8_t i1;\n"
  , "#define BitCast(GOT,WANT,b) ({ union { GOT got; WANT want; } ret; ret.got = (b); ret.want;})\n"
  , "#define ImplL(l)\n"
  , "#define ImplF(l)\n"
  , "#define VOID 0\n"
  , "typedef struct { u64 r; u64 rx; } Ret128;\n" -- c-call convention allows in-reg return of 2 u64s
  , "typedef Ret128 TArrow; typedef Ret128 TBound;\n"
  , "#define TSum(tagTy) struct { tagTy tag; union {\n"
  , "// Custom Defs //\n\n"
--, "#define BOX(ty,b) ({ty *p = malloc(sizeof(ty)); *p = (b); p;})\n"
--, "#define CastStruct(t1,t2,b) ({ union { t1 in; t2 out; } ret; ret.in= (b); ret.out;})\n"
  ]

emitCModule :: ModuleIName -> V.Vector LoadedMod -> V.Vector (LetMeta , Bind) -> DepPermutation -> Builder
emitCModule modIName loadedMods lets depPerm = let
  fnName lm = (letIName lm) & \q -> case lookupIName loadedMods (modName q) (unQName q) of
    Just hNm | modIName == modName q -> hNm
    got -> error $ show got <> ": " <> show q
  fnToStr (Right (fnDecl , fnBody)) = [fnDecl , " {\n  " , fnBody , "\n}\n"]
  fnToStr (Left  (fnDecl , fnBody)) = [fnDecl , " " , fnBody , ";\n\n"]
  -- TODO ensure the typedefs are in backpermuted order also!
  -- ! Don't have to precompute all ccs in that case
  (ccs , typedefs) = V.unzip $ lets <&> \(lm , (BindOK _ rhs)) -> let
    fName = encodeUtf8 (fnName lm)
    in (getCallingConv loadedMods fName rhs)
  binds = let
    emitFn (lm , (BindOK _ rhs)) cc = fnToStr $ emitFunction modIName loadedMods ccs (encodeUtf8 (fnName lm)) cc rhs
    in V.zipWith emitFn lets ccs
  in fromWriteList (writeByteString . unTypedef) (concat $ V.toList typedefs)
    <> fromWriteList writeByteString (concat $ V.toList (V.backpermute binds depPerm)) -- TODO improve perf

-- v ASM must also allocate the registers according to calling conv
getCallingConv :: V.Vector LoadedMod -> ByteString -> Expr -> (CallingConv , [Typedef])
getCallingConv loadedMods fnName (Core bindTerm ty) = let
--mkBasicTy nm = serialiseBasicTy loadedMods nm . tyToBasicTy
  mkAsmTy = tyToBasicTy . tyToAsmTy
  (argTys , retTy) = case ty of
    TyGround [THTyCon (THArrow ars ret)] -> (mkAsmTy <$> ars , mkAsmTy ret)
    TyGround [THBi _ (TyGround [THTyCon (THArrow ars ret)])]  -> (mkAsmTy <$> ars , mkAsmTy ret)
    -- TODO incomplete
    t -> (mempty , mkAsmTy t)

  maybeTypedef idx bty = if -- let tName = if idx < 0 then "" else "a" <> show idx in if
    | needsTypedef bty -> let
      td = fnName <> if idx < 0 then "_RT" else "_AT" <> show idx
      (bty' , rawTyStr) = serialiseBasicTy loadedMods (Just td) bty
      in ((bty' , td {-<> " " <> tName-}) , Just (Typedef $ "typedef " <> rawTyStr <> ";\n"))
    | True -> (serialiseBasicTy loadedMods Nothing bty , Nothing)

  nArgs = length argTys
  (retCC : argCC , maybeTypedefStrs) = unzip $ zipWith maybeTypedef [-1 .. nArgs -1] (retTy : argTys)
  typedefs = catMaybes maybeTypedefStrs

  in ((argCC , retCC) , typedefs)

tyToAsmTy (TyGround [th]) = th
tyToAsmTy t = error $ "asm: cannot codegen type: " <> toS (prettyTyRaw t)


impliedField :: BasicType -> Bool
impliedField = \case { BStruct bs -> BSM.size bs == 1 ; _ -> False }

-- ↓ next term , dups , retLoc (esp. ret typdef)
-- ↑ dependencies, literals, fns
-- ↓↑ state for the unfolding
data Env = Env { retVal :: BasicType , argEnv :: V.Vector (Value , BasicType) } deriving Show
data CSeed = Up BasicType | Dwn (Env , Term) deriving Show
termToCU :: ModIName -> V.Vector LoadedMod -> V.Vector CallingConv -> CSeed -> NextChunk CSeed
termToCU thisM loadedMods ccs (Up ty) = NEnd (Up ty)
termToCU thisM loadedMods ccs (Dwn (env , term)) = let
  idSeed t = Dwn (env , t)
  in case term of
  Return cast f  -> NEnclose ("return " <> cast) (idSeed f) ";"
  Lit l -> NStr (emitLiteral l) (Up $ BPrim (typeOfLit l))
  VBruijn v -> argEnv env V.! v & \(val , ty) -> let
    showValue = \case
      VArg i   -> ("a" <> show i)
      VLocal i -> ("l" <> show i)
      VLens v fields -> BS.intercalate "." (showValue v : fields)
    in NStr (showValue val) (Up ty)
  Var (VQBindIndex q) -> case lookupBindName loadedMods (modName q) (unQName q) of
    Just hNm -> NBStr (encodeUtf8 hNm) -- ! Get the calling conv
    got -> error $ show got <> ": " <> show q
  Cast cast x -> NSkip (idSeed x) -- Casts are incomplete, C/BetaEnv must insert them later
--  CastZext n -> let castStr = writeToByteString $ writeChar '(' <> emitPrimType (PrimNat n) <> writeChar ')'
--    in NChunks [Left castStr , Right (idSeed x) , Right (Up (BPrim (PrimNat n)))]

--  -- TODO cast tycons properly
--  CastFields fCasts -> NSkip (idSeed x)
--  CastProduct _n fCasts -> NSkip (idSeed x) -- TODO cast the fields, also β-env push down casts
--  CastSum bsm -> d_ bsm $ NSkip (idSeed x)
--  cast -> error $ show cast
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
-- TODO need arg typedefs => emit in topo order & pass down prev ccs
    Var (VQBindIndex q) | modName q == thisM -> let
      (ccArgs , ccRet) = ccs V.! unQName q
      -- if building a struct we need the arg typedef: eg. (FArgN){ ..fields.. }
      castArg (bty , strTy) arg = if
        | needsTypedef bty -> [Left " , " , Left ("(" <> strTy <> ")") , Right (idSeed arg)]
        | True -> [Left " , " , Right (idSeed arg)]
      mkArgs = alignWith (these (error . show) (error . show) castArg) ccArgs args
      in NChunks $ (Right (idSeed f) : Left "(" : drop 1 (concat mkArgs))
        ++ [Left ")"]
    _ -> NChunks $ (Right (idSeed f) : Left "(" : intersperse (Left " , ") (Right . idSeed <$> args))
     ++ [Left ")"]
  -- * Pass down type for prods and sums; sub-products split each field into a retLoc
  Prod bsm  -> let
    fList = BSM.toList bsm
    mkField (q , fieldVal) = getIName loadedMods (QName q) & \hNm ->
      [Left ("." <> hNm <> "=") , Right (idSeed fieldVal) , Left ", "]
    in case fList of
      [] -> NBStr "VOID"
      [(f1 , t)] -> NSkip (idSeed t)
      fList -> NChunks (Left "{ " : (concatMap mkField fList) ++ [Left "}"])
  -- The cast is an artefact of inference, TODO have infer. remove it / cast after extraction
  TTLens rawObj fields LensGet -> let
    mkAccess f = "." <> getIName loadedMods (QName f)
    in case rawObj of
    Cast (CastProduct 1 bsm) obj | [(idx , leafCast)] <- BSM.toList bsm -> -- TODO leafCast
      NEndStr (idSeed obj) (mconcat $ mkAccess <$> fields)
    obj ->
      NEndStr (idSeed obj) (mconcat $ mkAccess <$> fields)

  -- Labels are implicit until subtyped into a sumtype context
  Label l args -> NSkip (idSeed $ Prod (BSM.fromList (Prelude.imap (\i t -> (qName2Key (mkQName 0 i) , t)) args)))

  -- TODO calcScrut , default , LitTables , altCasts
  -- scrut = | Enum | Tag
  -- ! Must know scrut Type => To name it (scrut.tag , scrut.data) & interpret tag
  CaseB scrut inferredScrutTy alts d -> let -- BSM sorts on QName already, so can imap to get asmidxs TODO?
    last = BSM.size alts - 1
    mkAlt :: Maybe Value -> BasicType -> Int -> (Int , Term) -> [Either ByteString CSeed]
    mkAlt scrutNameM ty asmIdx (_qNm , term) = case ty of
      BSum nTags altTys maxSz -> let
        altTerm = case term of
          BruijnAbs n _ rhs -> rhs -- ! TODO ensure type matches this
          t -> t
        caseTxt = if asmIdx == last && isNothing d then "default: " else "case " <> show asmIdx <> ": "
        breakTxt = case altTerm of { Return{} -> "\n  "  ; _ -> "\n  " } -- break? not needed
        scrutLenses scrutName = let
          emitLens i (q , ty) = let
            unScrut = ["datum" , getIName loadedMods (QName q)]
            vlens = VLens scrutName (if impliedField ty then unScrut else unScrut ++ ["_" <> show i])
            in (vlens , ty)
          in V.imap emitLens (BSM.unBSM altTys)
        -- ! lift alt-fns OR need to remap deBruijns so the first n point to data in this label
        altEnv = Env (retVal env) case scrutNameM of
          Just nm -> (scrutLenses nm <> argEnv env)
          Nothing -> argEnv env
        in [Left caseTxt , Right (Dwn (altEnv , altTerm)) , Left breakTxt]
      BEnum n -> [Left ("case " <> show asmIdx <> ": ") , Right (idSeed term) , Left "\n  "]
      ty -> error $ show ty
    altList scrutName ty = (concat $ Prelude.imap (mkAlt scrutName ty) (BSM.toList alts))

    namedScrut scrutName scrutTy = Left "switch ("
      : Right (idSeed scrut)
      : Left (if isJust scrutName then ".tag) {\n  " else ") {\n  ")
      : altList scrutName scrutTy
      ++ [Left "}"]

    in case scrut of -- enums don't need a name, but all other scruts do
      VBruijn i -> argEnv env V.! i & \(scrutVal , ty) -> let
        seedRhs :: _ -> Term -> CSeed
        seedRhs tys = \case
          BruijnAbs n _free rhs -> let
            labelArgs = [0 .. n-1] <&> \i -> let fTy = tys V.! i
              in if V.length tys == 1 {- impliedField -} then (scrutVal , fTy) else (VLens scrutVal ["_" <> show i] , fTy)
            in Dwn (Env (retVal env) (V.fromList labelArgs <> argEnv env) , rhs)
          rhs -> idSeed rhs
        in case ty of
        BSum 1 sumTy maxSz | [(_q , subTys)] <- BSM.toList sumTy -> let
          tys = case subTys of { BStruct tys -> BSM.elems tys ; _ -> mempty } :: V.Vector BasicType
          in BSM.toList alts & \[(_q , rhs)] -> NSkip (seedRhs tys rhs)
        BSum nTags tys maxSz -> NChunks $ namedScrut (Just (VArg i)) ty
        BEnum nTags -> NChunks $ namedScrut Nothing ty
        t -> error $ show t
      -- TODO enum scruts don't need a name

--    calcEnumScrut -> NChunks $ namedScrut VVoid (BEnum (BSM.size alts)) False
      calcStruct -> let
        scrutTy = tyToBasicTy (unTyGround inferredScrutTy)
        readTag = case scrutTy of { BSum 1 _ _ -> False ; BEnum{} -> False ; BSum{} -> True }
        in NChunks $ namedScrut Nothing scrutTy
--      caseChunks = namedScrut (VLocal freshLocal) ty False
--      in NChunks $ (Left "({ " : {-Right (idSeed calcScrut) :-} caseChunks) ++ [Left "});"]
      -- anonScrut (d_ "warning: i32 assumed" $ BPrim (PrimInt 32)) True -- TODO bind the scrut onto a caseAlts

  X86Intrinsic "_mm256_undefined_si256" -> NBStr "_mm256_undefined_si256()"
  X86Intrinsic txt -> NBStr (encodeUtf8 txt)
  x -> error $ show x

needsTypedef = \case { BStruct{} -> True ; BSum{} -> True ; BArrow{} -> True ; _ -> False }

-- [typedefs] , ret_ty fnName(arg1Ty arg1Nm , t2 n2) { .. }
emitFunction :: ModuleIName -> V.Vector LoadedMod -> V.Vector CallingConv -> ByteString -> CallingConv -> Expr
  -> Either (ByteString , ByteString) (ByteString , ByteString)
emitFunction thisM loadedMods ccs fnName cc@(argT , retT) (Core term _) = let
  nArgs = length argT
  (retBTy  , retTyStr) = retT
  (argBTys , argTyStrs) = unzip argT

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
    t -> Return (if needsTypedef retBTy then "(" <> retTyStr <> ")" else "") t -- eg. "(retTy){.f=3}"

  fnDecl = {-typedefStrs <>-} retTyStr <> " " <> fnName <> "("
    <> BS.intercalate " , " (Prelude.imap (\i t -> t <> " a" <> show i) argTyStrs) <> ")"

  argValues = zipWith (\i ty -> (VArg i , ty)) [nArgs - 1 , nArgs - 2 .. 0] argBTys
  mkRhs rhs = snd $ unfoldrChunks (termToCU thisM loadedMods ccs) (Dwn (Env retBTy (V.fromList argValues) , rhs))
  in if nArgs == 0 && fnName /= "main"
    then Left ({-typedefStrs <>-} retTyStr <> " const " <> fnName <> " =" , mkRhs rhs)
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
emitPrimType p = writeByteString case p of
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
