{-# Language TemplateHaskell #-}
module CoreToX86 where
import qualified X86
import Externs
import CoreSyn
import Prim
import Data.Functor.Foldable
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified BitSetMap as BSM
import qualified Foreign.Storable
import qualified Data.IntMap as IM
import Control.Lens
import Foreign.Ptr
import PrettyCore

data CPUState = CPUState
 { _regs         :: V.Vector (Maybe Word64 , Int) -- register state (track constants)
-- , _flagCarry    :: Bool
-- , _flagOverflow :: Bool
 , _spills       :: [X86.Reg]
 }; makeLenses ''CPUState
startCPUState = CPUState mempty []

type NBits = Int
type SizeT = Int -- Word64 probably more useful on 64-bit pointer size system
data Value
  = Reg X86.Reg AsmType -- can index all registers incl xmm etc, based on asmtype
  | MMReg X86.Reg AsmType
--  | SubReg X86.Reg Int Int -- bitfield [i:n]
  | VProd (V.Vector Value) ProdType
  | VSum Value Value
  | VInstr PrimInstr -- dummy thing that never gets codegenned
  | VLit   Literal -- Some instructions take an immediate, so don't directly assign this to register
  | VFlagCarry -- boolean test
  deriving Show

type ProdType = (Int , BSM.BitSetMap AsmType) -- total bits needed
data AsmType
 = Bits Int -- most normal is 64 , can extend to any size but may spill. (16 ymm regs = 4096 bits)
 | ProdTy ProdType
 | SumTy Int (BSM.BitSetMap AsmType) Int -- number of alts, possible alts , largest Alt
-- | PackedBits Int (V.Vector Int) -- pack into registers using bitshifts
-- | Mem SizeT
 deriving Show

-- Setup: asm Functions typed by a single arrow: Product -> Product
--   coprods: frame header encoding sumtypes within the product
-- ? annotate nodes part of return product so can write to register/mem directly
-- ? Reg-mode: NeedSpill | NeedPack | ..
-- Prod/Lens -> Tuple/direct idx
-- BruijnAbsTyped -> specialise on fn as args ; so no non-top-level bruijnabs
-- Label/Case -> Switches ; labelApp only when subtype cast into a sumtype
-- Rectypes -> mk automata: linked-list tree of transition buffers + array for contents of each branch type
-- Paps -> fuse as much as possible, else mk explicit sumtypes
-- NoCode bindings(only codegen specs): anything specialisable on fns/paps/sum types

-- Generating x86: 
-- * cataM: compute branches (in parallel | interleave instructions) and ret
-- * Track (either immsizes dynsizes) + cpu & stack state
-- * loops + forward refs
-- * ret product presents an end goal to place registers in

asmSizeOf :: AsmType -> NBits
asmSizeOf = \case
  Bits n -> n
  ProdTy (p , _) -> p
  SumTy n p sz -> sizeOfTagBits n + sz -- sizeof gets number of bytes in an int
sizeOfTagBits n = Foreign.Storable.sizeOf n * 8 - countLeadingZeros n

data AsmState = AsmState
 { _cpuState   :: CPUState
 , _retLoc     :: Value
 , _memLen     :: Int
 , _memPtr     :: Ptr Word8 -- inc. with each write
 , _bruijnArgs :: V.Vector Value
-- , _fnEntry    :: Ptr Word8
 , _labels     :: (Int , IM.IntMap (Ptr Word8)) -- (label -> mem loc) for patching jmps / calls / sub rsp / ..
 }; makeLenses ''AsmState
newLabel = use memPtr >>= \ptr -> use labels >>= \(i , im) -> i <$ (labels .= (i + 1 , IM.insert i ptr im))
getLabel l = use labels <&> \(_ , im) -> im IM.! l

svState :: AsmM _
svState = use bruijnArgs >>= \ars -> use retLoc >>= \r -> use cpuState <&> \cps -> (ars , r , cps)
restoreState :: _ -> AsmM ()
restoreState (ars , r , cps) = (bruijnArgs .= ars) *> (retLoc .= r) *> (cpuState .= cps)

type AsmM = StateT AsmState IO

writeAsm :: [X86.Immediate] -> AsmM ()
writeAsm prog = use memPtr >>= \ptr -> use memLen >>= \len -> liftIO (X86.mkAsm len ptr prog) >>=
  \wroteLen -> memPtr %= \p -> plusPtr p wroteLen
writeAsmAt ptr prog = liftIO (X86.mkAsm 15 {-max len for an instruction-} ptr prog)

-- find best register(s) for subexpression e : ty; Either the ret location or a random spare register
getReg :: PrimType -> {-[X86.Reg] ->-} AsmM Value
getReg ty = pure (Reg X86.RAX (Bits 64))

-- TODO registers are always assumed clobberable
mkAsmBinInstr i lOp@VLit{} rOp = case i of
  -- TODO iff assoc!
  _ -> mkAsmBinInstr' i rOp lOp
mkAsmBinInstr i lOp rOp = mkAsmBinInstr' i lOp rOp

mkAsmBinInstr' :: PrimInstr -> Value -> Value -> AsmM Value
mkAsmBinInstr' i lOp rOp = case i of
  NumInstr ni -> case ni of
    IntInstr Add | v@(Reg l _) <- lOp -> case rOp of
      VLit (Fin 32 i) -> v <$ writeAsm (X86.addImm32 l (fromIntegral i))
      Reg r _ -> v <$ writeAsm (X86.addReg l r)
    x -> use retLoc <* d_ ("error: " <> show i <> " " <> show (lOp , rOp) :: Text) (writeAsm X86.hlt) -- 
  x -> error $ show x

-- TODO retloc'
mkAsmLiteral retLoc = \case
  Fin 32 i | Reg r _ <- retLoc -> writeAsm (X86.movImm32 r (fromIntegral i))
  Fin  8 i | Reg r _ <- retLoc -> writeAsm (X86.movImm32 r (fromIntegral i))
  x -> error $ show x

--mkAsmU :: ModuleIName -> V.Vector LoadedMod -> V.Vector Word32 -> AsmM
--mkAsmU thisM loadedMods localBinds = \case

mkAsmF :: ModuleIName -> V.Vector LoadedMod -> V.Vector Word32
  -> TermF (AsmM Value) -> AsmM Value
mkAsmF thisM loadedMods localBinds = let
  f = Reg X86.RAX (Bits 64) <$ writeAsm X86.hlt -- a TODO placeholder
  in \case
  VBruijnF i -> use bruijnArgs <&> (V.! i)
  VarF (VQBindIndex q) -> f
--LitF l -> (Fin 32 imm32) -> use retLoc >>= \(Reg r 32) -> movImm32 r imm32
  LitF l -> pure (VLit l)
  CastF c t -> f
  InstrF i -> pure (VInstr i)

  -- Figure out calling convention based on type of f: rip-relative
  AppF mkFn mkArgs -> sequence mkArgs >>= \args -> mkFn >>= \case
    VInstr i | [l , r] <- args -> mkAsmBinInstr i l r -- retloc?
    fn -> d_ fn f

  ArrayF ars -> _f
  TupleF ars -> _f
  TTLensF scrut [field] LensGet -> scrut >>= \case
    VProd regs (_ , tys) -> pure (regs V.! fst (BSM.findIndex tys field))
    x -> error $ show x

  LabelF l ars -> f -- do what tuple does, mk label only when subcasted into sumtype

  -- switches = cmp je , cmp je ..
  -- TODO cmov cases
  -- TODO can save the last jmp instruction
  CaseBF mkScrut _t alts Nothing -> mkScrut >>= \scrut -> svState >>= \savedState -> case scrut of
    VSum (Reg r (Bits s)) datum -> do
      labels <- V.generateM (BSM.size alts) $ \i -> do
        writeAsm (X86.cmpImm32 r (fromIntegral i))
        newLabel <* writeAsm (X86.jzImm32 0) -- placeholder jz
      (\go -> V.zipWithM go labels (BSM.elems alts)) $ \l mkAlt -> do
        restoreState savedState
        getLabel l >>= \comeFrom -> use memPtr >>= \ref ->
          writeAsmAt comeFrom (X86.jzImm32 (fromIntegral (minusPtr ref comeFrom) - X86.jmpImm32Sz))
        mkAlt
      use retLoc
    x -> error $ show x

  x -> error $ show (embed (Question <$ x))

-- * Convert types to asmTypes
-- * Compute Start state for function , alloc args , retloc , calling convention
-- ? using retloc registers before they are needed
exprToAsmSeed :: Expr -> (V.Vector Value , Value , Term)
exprToAsmSeed expr@(Core bindTerm ty) = let
  sizeOfProd pr = sum (asmSizeOf <$> pr)
  tyToAsmTy (TyGround [th]) = case th of
    THPrim (PrimInt n) -> Bits n
    THTyCon (THProduct bsm) -> tyToAsmTy <$> bsm & \prod -> ProdTy (sizeOfProd prod , prod)
    THTyCon (THTuple   bsm) -> tyToAsmTy <$> bsm & \prod ->
      ProdTy (sizeOfProd prod , BSM.fromList $ V.toList (V.indexed prod))
    THTyCon (THSumTy   bsm) -> tyToAsmTy <$> bsm & \prod -> let
      maxSz = maximum (asmSizeOf <$> prod)
      in SumTy (BSM.size prod) prod maxSz
    x -> error $ show x
  (argTys , retTy) = case ty of
    TyGround [THTyCon (THArrow ars retT)] -> (tyToAsmTy <$> ars , tyToAsmTy retT)
    t -> (mempty , tyToAsmTy t)
  nArgs = length argTys

  -- merge sumtype headers?
  -- the produced Value vector is 1:1 with VBruijns
  -- But a VBruijn may be distributed accross multiple registers + the stack
  allocArg :: ([AsmType] , [X86.Reg]) -> (Value , ([AsmType] , [X86.Reg]))
  allocArg (argT : argTys , freeRegs) = let
    in case argT of
    Bits n | n <= 64 ->
      Prelude.uncons freeRegs & \(Just (car , cdr)) -> (Reg car argT , (argTys , cdr))
    -- sortby size?
    ProdTy prodTy@(nbits , prod) | nbits <= 64 -> let
      nFields = BSM.size prod
      elems   = BSM.elems prod -- BSM.elems = sorted on QNames TODO sort on sizes?
      in unfoldrExactN' (V.length elems) allocArg (V.toList elems , freeRegs)
        & \(v , seed) -> (VProd v prodTy , seed)
    SumTy nAlts prod sz -> Prelude.uncons freeRegs & \(Just (tagReg , regs')) -> Prelude.uncons regs' &
      \(Just (dataReg , cdr)) -> let value = VSum (Reg tagReg (Bits (sizeOfTagBits nAlts))) (Reg dataReg (Bits sz))
        in (value , (argTys , cdr))
    x -> error $ show x
  allocArg ([] , _) = error "impossible"

  allocArgs = did_ $ V.unfoldrExactN nArgs allocArg (reverse argTys , X86.ccall_scratchRegs)
  allocRet  = fst $ allocArg ([retTy] , X86.RAX : X86.ccall_scratchRegs)
  in case bindTerm of
    BruijnAbs n body -> case compare nArgs n of
      EQ -> (allocArgs , allocRet , body)
      GT -> _pap
      LT -> error $ "impossible: function has non-function type: "
        <> toS (prettyTermRaw bindTerm) <> "\n: " <> toS (prettyTyRaw ty)
    term | nArgs == 0 -> (mempty , allocRet , term)
    _ -> error $ show (nArgs , bindTerm)

-- C calling conv = ret in rax, args in rdi, rsi, rdx, rcx, r8, r9 , rest on stack in rev order
-- callee saved = r[12..15] rsp, rbp
bindToAsm :: ModuleIName -> V.Vector LoadedMod -> V.Vector Word32 -> (Ptr Word8 , Int) -> Expr -> IO (Ptr Word8)
bindToAsm thisM loadedMods localBinds (memPtr' , memLen') expr = let
  -- Get calling convention from the function
  (argValues , retLoc , rhs) = exprToAsmSeed expr
  cgRet = \case
    Reg X86.RAX _ -> writeAsm X86.ret
    Reg r _       -> writeAsm (X86.movR64 X86.RAX r) *> writeAsm X86.ret
    x -> error $ show x
  cgBind = cata (mkAsmF thisM loadedMods localBinds) rhs >>= cgRet
  in do
  (_retValue , asmState) <- cgBind `runStateT` AsmState
    { _cpuState = startCPUState
    , _retLoc   = retLoc
    , _memLen   = memLen'
    , _memPtr   = memPtr'
    , _bruijnArgs = argValues
    , _labels   = (0 , mempty)
    }
  pure (asmState ^. memPtr)

-- * cg a module asm and write to a ptr
-- * track symbols = offset & strName
mkAsmBindings :: ModuleIName -> V.Vector LoadedMod -> V.Vector (LetMeta , Bind) -> (Ptr Word8 , Int)
  -> IO (Ptr Word8 , (Maybe Word64 , [(Word64 , ByteString)])) -- return endPtr and entrypoint relative to start of .txt section
mkAsmBindings modIName loadedMods lets (memPtr , memLen) = let
  bindOffs = mempty -- offsets to previously defined bindings (also needed for emitting symbols)
  -- sequentially write out all functions & collect their offsets for strtable purposes
  appendBind (ptr , offs) (lm , bind) = let
    nm = (letBindIndex lm) & \(VQBindIndex q) -> lookupBindName loadedMods (modName q) (unQName q)
    in case bind of
    BindOK opt rhs -> bindToAsm modIName loadedMods bindOffs (ptr , memLen) rhs -- TODO memlen
      <&> \endPtr -> (endPtr , maybe offs (\nm -> (fromIntegral (minusPtr ptr memPtr) , encodeUtf8 nm) : offs) nm)
    b -> error $ show b
  in do
  entryEndPtr <- X86.mkAsm' memLen memPtr (concat X86.exitSysCall) -- (concat X86.writeSysCall)
  let entrySym = [(0 , "start")]
  (endPtr , syms) <- foldM appendBind (entryEndPtr , entrySym) lets
  pure (endPtr , (Just (fromIntegral $ minusPtr endPtr memPtr) , syms)) -- main entry is our exit syscall
