{-# Language TemplateHaskell #-}
module CoreToX86 where
import qualified X86
import Externs
import CoreSyn
import Prim
import Data.Functor.Foldable
import Data.Functor.Foldable.TH
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified BitSetMap as BSM
import qualified Foreign.Storable
import qualified Data.IntMap as IM
import Control.Lens
import Foreign.Ptr
import PrettyCore

-- 0. pre-name the arg and return registers
-- 1. ↓ Convert to register machine, max overlap registers, rm {} and [] types, assign reg types
-- 2. ↑ allocate registers|flags|stack insert call/jmp addresses
type RName = Int -- Encode different reg types and enumerate separately
data MiniCore
  = SetLit    RName Literal
  | ArgReg    RName
  | Instr2    RName PrimInstr MiniCore MiniCore
  | Instr2Imm RName PrimInstr MiniCore Literal
  | CallQName RName QName [MiniCore]
  | Switch    RName MiniCore [Int] [MiniCore] -- scrut , register surviving , alts
  deriving Show; makeBaseFunctor ''MiniCore
--data IRFunction = IRFunction CallingConv QName

data RegMachineState = RegMachineState
  { _freshReg :: Int , _argRegs :: V.Vector RName }; makeLenses ''RegMachineState
-- ↓ Convert to register machine, re-using as many as possible , rm {} []
-- At leaves, the cata will find register names indicating how many distinct registers the sequence needs
mkRegMachineU :: (RegMachineState , Term) -> MiniCoreF (RegMachineState , Term)
mkRegMachineU (st , term) = case term of
  Lit l      -> SetLitF (st ^. freshReg) l
  VBruijn i  -> ArgRegF ((st ^. argRegs) V.! i) -- cata can (maybe) re-use these regs
  -- v First branch may re-use ret-reg , second branch must find itself a new reg
  App i@Instr{} [lOp , rOp]   -> Instr2F (st ^. freshReg) i st (st . freshReg %~ (1+))
  App i@Instr{} [lOp , Lit l] -> Instr2ImmF (st ^. freshReg) i st l
  App f args -> _

-- ↑ Allocate registers (maybe spill) , incl retReg to best RName , insert exact jmp/call addresses
-- * first n regs are the ret-regs
-- * argRegs (the next m regs) are predetermined
-- * else assign regs 'arbitrarily' and swap some to stack if necessary
mkX86F :: MiniCoreF (IO ()) -> IO ()
mkX86F = _

genAsm term = hylo mkX86F mkRegMachineU (RegMachineState 0 mempty , term)

tailRecurse :: (st -> IO (Value , st)) -> st -> IO st 
tailRecurse next = h where
  h = next >=> \case
    (Ret , st) -> pure st
    (val , st) -> h st

type NBits = Int
type SizeT = Int -- Word64 probably more useful on 64-bit pointer size system
data CPUFlag = ZFlag | OFlag | CFlag deriving Show
data Value
  = Reg X86.Reg AsmType -- can index all registers incl xmm etc, based on asmtype
  | MMReg X86.Reg AsmType
--  | SubReg X86.Reg Int Int -- bitfield [i:n]
  | VProd (V.Vector Value) ProdType
  | VSum Value Value
  | VInstr PrimInstr -- dummy thing that never gets codegenned
  | VAddr (Ptr Word8) CallingConv -- absolute
  | VLit   Literal -- Some instructions take an immediate, so don't directly assign this to register
  | VFlag CPUFlag -- boolean test
  | Void
  | Ret
  deriving Show

type LiveRegs = Word16 -- Word32 -- Bitset for regs and MM regs
setReg :: LiveRegs -> X86.Reg -> LiveRegs
setReg live r = setBit live (fromEnum r)
allocReg :: LiveRegs -> (X86.Reg , LiveRegs)
allocReg live = if live == complement 0 then error "no free regs"
  else countLeadingZeros live & \r -> (toEnum r , setBit live r) -- setBit live (fromEnum r)
freeReg :: X86.Reg -> LiveRegs -> LiveRegs
freeReg r live = fromEnum r & \ri -> if testBit live ri then clearBit live ri else error $ show (live , r)
-- v TODO slow
getLiveRegs live = toEnum <$> bitSet2IntList (fromIntegral live)

type ProdType = (Int , BSM.BitSetMap AsmType) -- total bits needed
data AsmType
 = Bits Int -- can be any size and may span multiple registers / spill. (16 ymm regs = 4096 bits)
 | ProdTy ProdType
 | SumTy Int (BSM.BitSetMap AsmType) Int -- number of alts, possible alts , largest Alt
-- | PackedProd Int (V.Vector Int) -- pack into registers using bitshifts
-- | Mem SizeT
 deriving (Show , Eq)

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

type CallingConv = (V.Vector Value , Value)
-- * Convert types to asmTypes
-- * Compute Start state for function , alloc args , retloc , calling convention
-- ? using retloc registers before they are needed
getCallingConv :: Expr -> CallingConv
getCallingConv expr@(Core bindTerm ty) = let
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
  tyToAsmTy t = error $ "asm: cannot codegen type: " <> toS (prettyTyRaw t)
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

  allocArgs = V.unfoldrExactN nArgs allocArg (reverse argTys , X86.ccall_scratchRegs)
  allocRet  = fst $ allocArg ([retTy] , X86.RAX : X86.ccall_scratchRegs)
  in (allocArgs , allocRet)

asmSizeOf :: AsmType -> NBits
asmSizeOf = \case
  Bits n -> n
  ProdTy (p , _) -> p
  SumTy n p sz -> sizeOfTagBits n + sz -- sizeof gets number of bytes in an int
sizeOfTagBits n = Foreign.Storable.sizeOf n * 8 - countLeadingZeros n

data AsmState = AsmState
 { _retLoc     :: Value
 , _memLen     :: Int
 , _memPtr     :: Ptr Word8 -- inc. with each write
 , _bruijnArgs :: V.Vector Value
 , _liveRegs   :: LiveRegs
-- , _labels     :: (Int , IM.IntMap (Ptr Word8)) -- (label -> mem loc) for patching jmps / calls / sub rsp / ..
 , _topExpr    :: Bool
 , _modBinds   :: MV.IOVector (CallingConv , Either [Word32] (Ptr Word8))
 }; makeLenses ''AsmState
voidAddr = complement 0 :: Word32

--newLabel :: AsmM s Int
--newLabel = use memPtr >>= \ptr -> use labels >>= \(i , im) -> i <$ (labels .= (i + 1 , IM.insert i ptr im))
--getLabel l = use labels <&> \(_ , im) -> im IM.! l

svState :: AsmM s _
svState = use bruijnArgs >>= \ars -> use retLoc <&> \r -> (ars , r)
restoreState :: _ -> AsmM s ()
restoreState (ars , r) = (bruijnArgs .= ars) *> (retLoc .= r)

type AsmM s = StateT (AsmState) IO

writeAsm :: [X86.Immediate] -> AsmM s ()
writeAsm prog = use memPtr >>= \ptr -> use memLen >>= \len -> liftIO (X86.mkAsm len ptr prog) >>=
  \wroteLen -> memPtr %= \p -> plusPtr p wroteLen
writeAsmAt ptr prog = liftIO (X86.mkAsm 15 {-max len for an instruction-} ptr prog)

-- find best register(s) for subexpression e : ty; Either the ret location or a random spare register
getReg :: PrimType -> {-[X86.Reg] ->-} AsmM s Value
getReg ty = pure (Reg X86.RAX (Bits 64))

-- TODO registers are always assumed clobberable
-- TODO iff assoc
mkAsmBinInstr i lOp@(VLit (Fin 32 imm)) rOp | isAssoc i = mkAsmBinInstrImm32 i rOp (fromIntegral imm)
mkAsmBinInstr i lOp rOp@(VLit (Fin 32 imm)) = mkAsmBinInstrImm32 i lOp (fromIntegral imm)
mkAsmBinInstr i lVal@(Reg l _) (Reg r _) = case i of
  NumInstr ni -> case ni of
    IntInstr Add -> lVal <$ writeAsm (X86.addReg l r) 
    IntInstr Mul -> lVal <$ writeAsm (X86.iMul64Reg l r) 

mkAsmBinInstrImm32 :: PrimInstr -> Value -> Word32 -> AsmM s Value
mkAsmBinInstrImm32 i lOp imm = case i of
  NumInstr ni -> case ni of
    IntInstr Add    | v@(Reg l _) <- lOp -> v <$ writeAsm (X86.addImm32 l (fromIntegral imm))
    IntInstr Sub    | v@(Reg l _) <- lOp -> v <$ writeAsm (X86.subImm32 l (fromIntegral imm))
    PredInstr LTCmp | v@(Reg l _) <- lOp -> VFlag ZFlag <$ writeAsm (X86.cmpImm32 l (fromIntegral imm))
    x -> use retLoc <* d_ ("error: " <> show i <> " " <> show (lOp , imm) :: Text) (writeAsm X86.hlt)
  x -> error $ show x
-- Reg r _ -> v <$ writeAsm (X86.addReg l r)
-- Reg r _ -> VFlag ZFlag <$ writeAsm (X86.cmpReg l r)

-- TODO retloc'
mkAsmLiteral retLoc = \case
  Fin 32 i | Reg r _ <- retLoc -> writeAsm (X86.movImm32 r (fromIntegral i))
  Fin  8 i | Reg r _ <- retLoc -> writeAsm (X86.movImm32 r (fromIntegral i))
  x -> error $ show x

respectRetLoc :: Value -> AsmM s Value
respectRetLoc lv@(Reg l t2) = use retLoc >>= \rv@(Reg r t1) -> if
  | t1 /= t2 -> error $ "type mismatch: " <> show (t1 , t2) -- TODO assertion
  | r == l -> pure rv
  | True -> rv <$ writeAsm (X86.movR64 r l)
respectRetLoc lv@(VLit (Fin fn l)) = use retLoc >>= \rv@(Reg r t1) -> case t1 of
  Bits n | n <= 32 , fn <= 32 -> rv <$ writeAsm (X86.movImm32 r (fromIntegral l))
  t -> error $ show t
respectRetLoc lv = error $ show (lv)

mkAsmF :: ModuleIName -> V.Vector LoadedMod -> TermF (AsmM s Value) -> AsmM s Value
mkAsmF thisM loadedMods = let
  in \case
  VBruijnF i -> use bruijnArgs <&> (V.! i)
  VarF (VQBindIndex q) | modName q == thisM -> use modBinds >>= \v -> liftIO (MV.read v (unQName q)) >>= \case
    (cc , Right addr) -> pure (VAddr addr cc)
    (cc , Left{}    ) -> error ("forward ref: " <> showRawQName q) -- TODO topological sort?
  LitF l -> use topExpr >>= \canRet -> if canRet then respectRetLoc (VLit l) *> writeAsm X86.ret $> Ret else pure (VLit l)
  CastF c t -> _f
  InstrF i -> pure (VInstr i)

  -- Setup arg retLocs , push clobbered regs & generate args
  AppF mkFn mkArgs -> (topExpr <<.= False) >>= \isTop -> mkFn >>= \case
    VInstr i -> do
      svRetLoc <- use retLoc
      -- TODO type for retloc?!
      args <- mkArgs `forM` \mkArg -> ((liveRegs %%= allocReg) >>= \r -> retLoc .= Reg r (Bits 32)) *> mkArg
      retLoc .= svRetLoc
      case args of
        [l , r] -> mkAsmBinInstr i l r >>= \case
          v@VFlag{} -> pure v
          x -> respectRetLoc x
    VAddr addr (ccArgs , ccRet) -> do
      svRetLoc <- use retLoc
      -- arg retLocs will overwrite things we may be using
      let genArg = \case
            These cc mkVal -> (retLoc .= cc) *> mkVal
            _ -> error "calling conv arity mismatch"
        in sequence $ alignWith genArg (V.toList ccArgs) mkArgs
      retLoc .= svRetLoc
      liveRegs <- getLiveRegs <$> use liveRegs
      liveRegs `forM` \r -> writeAsm (X86.push r)

      ref <- use memPtr
      writeAsm (X86.callImm32 (fromIntegral (minusPtr addr ref) - X86.callRelativeSz))
      liveRegs `forM_` \r -> writeAsm (X86.pop32 r) -- TODO 32?
      respectRetLoc ccRet
    fn -> _f

  ArrayF ars -> _f
  TupleF ars -> _f
  TTLensF scrut [field] LensGet -> scrut >>= \case
    VProd regs (_ , tys) -> pure (regs V.! fst (BSM.findIndex tys field))
    x -> error $ show x

  LabelF l ars -> _f -- do what tuple does, mk label only when subcasted into sumtype

  -- switches = cmp je , cmp je ..
  -- TODO cmov cases
  -- TODO can save the last jmp instruction
  -- TODO if top-level, can jmp out of the case
  CaseBF mkScrut _t alts Nothing -> let
    patchLabel comeFrom ref jmpTy = writeAsmAt comeFrom
      (jmpTy (fromIntegral (minusPtr ref comeFrom) - X86.jmpCondImm32Sz))
    patchJmp comeFrom ref = writeAsmAt comeFrom (X86.jmpImm32 (fromIntegral (minusPtr ref comeFrom) - X86.jmpImm32Sz))
    in use topExpr >>= \canRet -> mkScrut >>= \case
    -- flags are already set
    VFlag ZFlag | BSM.size alts == 2 , [ok , ko] <- V.toList (BSM.elems alts) -> do
      startPtr <- use memPtr <* writeAsm (X86.jnzImm32 0)
      ok
      use memPtr >>= \koPtr -> patchLabel startPtr koPtr X86.jnzImm32
      endbr <- if canRet then Nothing <$ writeAsm X86.ret else Just <$> (use memPtr <* writeAsm (X86.jmpImm32 0))
      ko -- TODO restore cpu state to beginning of switch case for alts!
      endPtr <- use memPtr
      for_ endbr $ \e -> patchLabel e endPtr X86.jmpImm32
      if canRet then Ret <$ writeAsm X86.ret else use retLoc
--  Reg r (Bits s) -> mkSwitch r Nothing
--  VSum (Reg r (Bits s)) datum -> mkSwitch r (Just datum)
    x -> error $ show x
  x -> error $ show (embed (Question <$ x))

getRhs :: Int -> Expr -> Term
getRhs nArgs (Core term ty) = case term of
  BruijnAbs n body -> case compare nArgs n of
    EQ -> body
    GT -> _pap
    LT -> error $ "impossible: function has non-function type: "
      <> toS (prettyTermRaw term) <> "\n: " <> toS (prettyTyRaw ty)
  term | nArgs == 0 -> term
  _ -> error $ show (nArgs , term)

-- C calling conv = ret in rax, args in rdi, rsi, rdx, rcx, r8, r9 , rest on stack in rev order
-- callee saved = r[12..15] rsp, rbp
bindToAsm :: ModuleIName -> V.Vector LoadedMod -> MV.IOVector _ -> (Ptr Word8 , Int) -> Int -> Expr -> IO (Ptr Word8)
bindToAsm thisM loadedMods mb (memPtr' , memLen') bindINm expr = let
  -- Get calling convention from the function
  (argValues , retValue) = getCallingConv expr
  live = V.foldl (\live (Reg r _) -> setReg live r) 0 argValues
  rhs = getRhs (V.length argValues) expr
  cgRet = \case
    Ret           -> pure ()
    v             -> writeAsm X86.ret
    x -> error $ show x
  startState = AsmState
    { _retLoc   = retValue
    , _memPtr   = memPtr' , _memLen   = memLen'
    , _liveRegs = live
    , _bruijnArgs = argValues
--  , _labels   = (0 , mempty)
    , _topExpr  = True
    , _modBinds = mb
    }
  cgBind = cata (mkAsmF thisM loadedMods) rhs >>= cgRet
--cgBind2 = tailRecurse mkAsmU (rhs , startState)
  in do
--traceShowM (bitSet2IntList $ fromIntegral live)
  MV.modify mb (\(cc , _) -> (cc , Right memPtr')) bindINm
  (_ , st) <- cgBind `runStateT` startState
  pure (st ^. memPtr)

-- * cg a module asm and write to a ptr
-- * track symbols = offset & strName
mkAsmBindings :: ModuleIName -> V.Vector LoadedMod -> V.Vector (LetMeta , Bind) -> (Ptr Word8 , Int)
  -> IO (Ptr Word8 , (Maybe Word64 , [(Word64 , ByteString)])) -- return endPtr and entrypoint relative to start of .txt section
mkAsmBindings modIName loadedMods lets (memPtr , memLen) = let
  -- sequentially write out all functions & collect their offsets for strtable purposes
  appendBind modBinds (ptr , offs) (lm , bind) = let
    bindQName = (letBindIndex lm) & \(VQBindIndex q) -> q
    nm = lookupBindName loadedMods (modName bindQName) (unQName bindQName)
    in case bind of
    BindOK opt rhs -> bindToAsm modIName loadedMods modBinds (ptr , memLen) (unQName bindQName) rhs -- TODO memlen
      <&> \endPtr -> (endPtr , maybe offs (\nm -> (fromIntegral (minusPtr ptr memPtr) , encodeUtf8 nm) : offs) nm)
    b -> error $ show b
  in do
--modBinds <- MV.replicate (V.length lets) (Left [])
  modBinds <- V.unsafeThaw $ lets <&> \(_lm , (BindOK _ rhs)) -> (getCallingConv rhs , Left [])
  entryEndPtr <- X86.mkAsm' memLen memPtr (concat X86.exitSysCall) -- (concat X86.writeSysCall)
  let entrySym = [(0 , "start")]
  (endPtr , syms) <- foldM (appendBind modBinds) (entryEndPtr , entrySym) lets
  pure (endPtr , (Just (fromIntegral $ minusPtr endPtr memPtr) , syms)) -- main entry is our exit syscall
