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

type NBits = Int
type SizeT = Int -- Word64 probably more useful on 64-bit pointer size system
data CPUFlag = ZFlag | OFlag | CFlag deriving Show
data Value
  = Reg X86.Reg AsmType -- can index all registers incl xmm etc, based on asmtype
  | VProd (V.Vector Value) ProdType
  | VJmpCond X86.JmpCond
  | VSum Value Value deriving (Show , Eq)

data AsmType
 = Bits Int -- can be any size and may span multiple registers / spill. (16 ymm regs = 4096 bits)
 | ProdTy ProdType
 | SumTy Int (BSM.BitSetMap AsmType) Int -- number of alts, possible alts , largest Alt
 deriving (Show , Eq)
type CallingConv = (V.Vector Value , Value)
type ProdType = (Int , BSM.BitSetMap AsmType) -- total bits needed

-- 0. pre-name the arg and return registers
-- 1. ↓ Convert to register machine, max overlap registers, rm {} and [] types, assign reg types
-- 2. ↑ allocate registers|flags|stack insert call/jmp addresses
type RName = Int -- Encode different reg types and enumerate separately
data MiniCore
  = SetLit    RName Literal
  | ArgReg    Int
  | RenameArg RName Int
  | Dup       RName RName
  | CallQName Bool {- tailCall -} (Maybe RName) QName [MiniCore]
  | Instr2    PrimInstr MiniCore MiniCore -- ret reg is the left one , will be overwritten
  | InstrImm2 PrimInstr MiniCore Literal
  | IfElse Bool MiniCore MiniCore MiniCore -- TODO How to merge return types ? Need to ensure all subtyped properly
--  | Switch    RName MiniCore [Int] [MiniCore] -- scrut , register surviving , alts
  | Ret MiniCore
  deriving Show; makeBaseFunctor ''MiniCore
deriving instance Show (MiniCoreF ())
--data IRFunction = IRFunction CallingConv QName

data RegMachineState = RegMachineState
  { _freshReg :: Int , _retLoc :: Maybe Int }; makeLenses ''RegMachineState
-- ↓ Convert to register machine (rm {} []). re-use regs as much as possible
-- At leaves, the cata will find register names indicating how many distinct registers the sequence needs
mkRegMachineU :: Bool -> (RegMachineState , Term) -> MiniCoreF (RegMachineState , Term)
mkRegMachineU isTop (st , term) = case term of
  Top t       -> case t of -- We care about tail calls and ret-ting out of branches
    CaseB{}     -> mkRegMachineU True (st , t)
    App Var{} _ -> mkRegMachineU True (st , t)
    t       -> RetF (st , t)
  Lit l       -> SetLitF (fromMaybe (st ^. freshReg) (st ^. retLoc)) l
  VBruijn i   -> maybe (ArgRegF i) (\r -> RenameArgF r i) (st ^. retLoc)
  -- v First branch may re-use ret-reg , second branch must find itself a new reg
  -- also push down the retLoc for the lOp to use
  -- TODO rename all Instr1 to Casts
  App (Instr i) [lOp , rOp] -- may assume immediates are in rOp , simplifier reassociates if possible
    | Lit imm <- rOp -> InstrImm2F i (st , lOp) imm
    | otherwise -> Instr2F i (st , lOp) (st & freshReg %~ (1+) & retLoc .~ Nothing , rOp)
  App (Var (VQBindIndex q)) args -> let -- TODO prepare retloc for arg slots?
    st' = st & retLoc .~ Nothing
    in CallQNameF isTop (st ^. retLoc) q (zipWith (\i arg -> (st' & freshReg %~ (i+) , arg)) [0..] args)

  -- v Case alts are sorted by BSM , so first alt is always 0
  CaseB mkScrut _t alts Nothing | BSM.size alts == 2 , [ok , ko] <- V.toList (BSM.elems alts) ->
    -- Branches share same initial states since will run disjoint
    IfElseF isTop (st & retLoc .~ Nothing , mkScrut) (st , Top ok) (st , Top ko)

  x -> error $ show x

-- ↑ Allocate registers (maybe spill) , incl retReg to best RName , insert exact jmp/call addresses
-- * first n regs are the ret-regs
-- * argRegs (the next m regs) are predetermined
-- * else assign regs 'arbitrarily' and swap some to stack if necessary
data MkX86State = MkX86State
  { _memPtr   :: Ptr Word8
  , _memLen   :: Int
  , _modBinds :: MV.IOVector (CallingConv , Either [Word32] (Ptr Word8))
  , _liveRegs :: Word16 -- bitset
  , _argRegs  :: V.Vector Value
  }; makeLenses ''MkX86State

type MkX86M = StateT MkX86State IO
svState = use liveRegs :: MkX86M _
restoreState live = liveRegs .= live
writeAsm :: [X86.Immediate] -> MkX86M ()
writeAsm prog = use memPtr >>= \ptr -> use memLen >>= \len -> liftIO (X86.mkAsm len ptr prog) >>=
  \wroteLen -> memPtr %= \p -> plusPtr p wroteLen
writeAsmAt ptr prog = liftIO (X86.mkAsm 15 {-max len for an instruction-} ptr prog)

allocReg :: RName -> MkX86M X86.Reg
allocReg i = liveRegs %%= \l -> if l == 0 then error "no free regs"
  else countTrailingZeros l & \r -> (toEnum r , clearBit l r)
freeReg :: X86.Reg -> MkX86M ()
freeReg r = liveRegs %= (`setBit` fromEnum r)

-- Finally inverse the AST: @leaf: regName - argRegs = number of registers needed to compute the branch
-- There is some conflict between retLoc and argRegs
--   -> retLoc is pushed down and argReg renamed to free it quickly
--   TODO sometimes merge into a lea / 3-op xmm instruction
--mkX86F :: MiniCoreF (MkX86M X86.Reg) -> MkX86M X86.Reg
mkX86F :: MiniCoreF (MkX86M Value) -> MkX86M Value
mkX86F = \case
  SetLitF r (Fin n imm) | n <= 32 -> allocReg r >>= \reg -> writeAsm (X86.movImm32 reg (fromIntegral imm))
    $> Reg reg (Bits 32)
  ArgRegF i      -> use argRegs <&> (V.! i) -- <&> \(Reg r _) -> r
  RenameArgF r i -> use argRegs <&> (V.! i) >>= \(Reg argReg rty) ->
    allocReg r >>= \reg -> Reg reg rty <$ freeReg argReg <* writeAsm (X86.movR64 reg argReg)
  -- v ret reg is l, can free mkR reg
  InstrImm2F i mkL (Fin n imm) | n <= 32 -> mkL >>= \lV@(Reg l _) -> case i of
    NumInstr (IntInstr Add)  -> writeAsm (X86.addImm32 l (fromIntegral imm)) $> lV
    NumInstr (IntInstr Sub)  -> writeAsm (X86.subImm32 l (fromIntegral imm)) $> lV
    NumInstr (PredInstr pred) -> writeAsm (X86.cmpImm32 l (fromIntegral imm)) $> VJmpCond (case pred of
      LTCmp -> X86.JL ; GECmp -> X86.JNL ; LECmp -> X86.JLE ; GTCmp -> X86.JNLE
      EQCmp -> X86.JZ ; NEQCmp -> X86.JNZ
      )
    x -> error $ show x
  Instr2F i mkL mkR -> let
    x86Instr = case i of
      NumInstr (IntInstr Mul) -> X86.iMul64Reg
      NumInstr (IntInstr Add) -> X86.addReg
      NumInstr (IntInstr Sub) -> X86.subReg
    in mkL >>= \lv@(Reg l _) -> mkR >>= \rv@(Reg r _) -> writeAsm (x86Instr l r) *> freeReg r $> lv
--  NumInstr (IntInstr Sub)  -> v <$ writeAsm (X86.subImm32 l (fromIntegral imm))
--  PredInstr LTCmp -> VFlag ZFlag <$ writeAsm (X86.cmpImm32 l (fromIntegral imm))

  CallQNameF tailCall maybeRL q mkArgs {-| modName q == thisM-} -> use modBinds >>= \v ->
    liftIO (MV.read v (unQName q)) >>= \case
    (cc , Left{}    ) -> error ("forward ref: " <> showRawQName q) -- TODO topological sort?
    (cc@(argCC , retVal@(Reg retR _)) , Right addr) -> do
      sequence mkArgs
      ref <- use memPtr
      retVal <$ if tailCall
      then writeAsm (X86.jmpImm32 (fromIntegral (minusPtr addr ref) - X86.jmpImm32Sz))
      else writeAsm (X86.callImm32 (fromIntegral (minusPtr addr ref) - X86.callRelativeSz))

  IfElseF canRet cond ok ko -> let
    patchLabel jmpSz comeFrom ref jmpTy = writeAsmAt comeFrom
      (X86.jmpCondImm32 jmpTy (fromIntegral (minusPtr ref comeFrom) - jmpSz))
    patchJmp comeFrom ref = writeAsmAt comeFrom (X86.jmpImm32 (fromIntegral (minusPtr ref comeFrom) - X86.jmpImm32Sz))
    in do
    VJmpCond jmpCond <- cond -- TODO get the actual cond
    startState <- svState

    startPtr <- use memPtr <* writeAsm (X86.jmpCondImm32 jmpCond 0)
    okRet <- ok
    restoreState startState
    endOkBr <- if canRet then pure Nothing else Just <$> (use memPtr <* writeAsm (X86.jmpImm32 0))

    use memPtr >>= \koPtr -> patchLabel X86.jmpCondImm32Sz startPtr koPtr jmpCond
    koRet <- ko -- TODO restore cpu state to beginning of switch case for alts!
    restoreState startState

    for_ endOkBr $ \e -> use memPtr >>= \ref ->
      writeAsmAt e (X86.jmpImm32 (fromIntegral (minusPtr ref e) - X86.jmpImm32Sz))
    when (okRet /= koRet) (error $ show (okRet , koRet))
    pure okRet

  RetF i -> i <* writeAsm X86.ret
  x -> error $ show (() <$ x)

-- retReg is assigned to [V.length argRegs ..]
genAsm argVals retVal term = let
  start = (RegMachineState (V.length argVals + 1) (Just (V.length argVals)) , Top term)
  in -- d_ (ana mkRegMachineU start :: MiniCore) $
    hylo mkX86F (mkRegMachineU False) start

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

--mkAsmF :: ModuleIName -> V.Vector LoadedMod -> TermF (AsmM s Value) -> AsmM s Value
--mkAsmF thisM loadedMods = let
--  in \case
--  VBruijnF i -> use bruijnArgs <&> (V.! i)
--  VarF (VQBindIndex q) | modName q == thisM -> use modBinds >>= \v -> liftIO (MV.read v (unQName q)) >>= \case
--    (cc , Right addr) -> pure (VAddr addr cc)
--    (cc , Left{}    ) -> error ("forward ref: " <> showRawQName q) -- TODO topological sort?
--  LitF l -> use topExpr >>= \canRet -> if canRet then respectRetLoc (VLit l) *> writeAsm X86.ret $> Ret else pure (VLit l)
--  CastF c t -> _f
--  InstrF i -> pure (VInstr i)
--
--  -- Setup arg retLocs , push clobbered regs & generate args
--  AppF mkFn mkArgs -> (topExpr <<.= False) >>= \isTop -> mkFn >>= \case
--    VInstr i -> do
--      svRetLoc <- use retLoc
--      -- TODO type for retloc?!
--      args <- mkArgs `forM` \mkArg -> ((liveRegs %%= allocReg) >>= \r -> retLoc .= Reg r (Bits 32)) *> mkArg
--      retLoc .= svRetLoc
--      case args of
--        [l , r] -> mkAsmBinInstr i l r >>= \case
--          v@VFlag{} -> pure v
--          x -> respectRetLoc x
--    VAddr addr (ccArgs , ccRet) -> do
--      svRetLoc <- use retLoc
--      -- arg retLocs will overwrite things we may be using
--      let genArg = \case
--            These cc mkVal -> (retLoc .= cc) *> mkVal
--            _ -> error "calling conv arity mismatch"
--        in sequence $ alignWith genArg (V.toList ccArgs) mkArgs
--      retLoc .= svRetLoc
--      liveRegs <- getLiveRegs <$> use liveRegs
--      liveRegs `forM` \r -> writeAsm (X86.push r)
--
--      ref <- use memPtr
--      writeAsm (X86.callImm32 (fromIntegral (minusPtr addr ref) - X86.callRelativeSz))
--      liveRegs `forM_` \r -> writeAsm (X86.pop32 r) -- TODO 32?
--      respectRetLoc ccRet
--    fn -> _f
--
--  ArrayF ars -> _f
--  TupleF ars -> _f
--  TTLensF scrut [field] LensGet -> scrut >>= \case
--    VProd regs (_ , tys) -> pure (regs V.! fst (BSM.findIndex tys field))
--    x -> error $ show x
--
--  LabelF l ars -> _f -- do what tuple does, mk label only when subcasted into sumtype
--
--  -- switches = cmp je , cmp je ..
--  -- TODO cmov cases
--  -- TODO can save the last jmp instruction
--  -- TODO if top-level, can jmp out of the case
--  CaseBF mkScrut _t alts Nothing -> let
--    patchLabel comeFrom ref jmpTy = writeAsmAt comeFrom
--      (jmpTy (fromIntegral (minusPtr ref comeFrom) - X86.jmpCondImm32Sz))
--    patchJmp comeFrom ref = writeAsmAt comeFrom (X86.jmpImm32 (fromIntegral (minusPtr ref comeFrom) - X86.jmpImm32Sz))
--    in use topExpr >>= \canRet -> mkScrut >>= \case
--    -- flags are already set
--    VFlag ZFlag | BSM.size alts == 2 , [ok , ko] <- V.toList (BSM.elems alts) -> do
--      startPtr <- use memPtr <* writeAsm (X86.jnzImm32 0)
--      ok
--      use memPtr >>= \koPtr -> patchLabel startPtr koPtr X86.jnzImm32
--      endbr <- if canRet then Nothing <$ writeAsm X86.ret else Just <$> (use memPtr <* writeAsm (X86.jmpImm32 0))
--      ko -- TODO restore cpu state to beginning of switch case for alts!
--      endPtr <- use memPtr
--      for_ endbr $ \e -> patchLabel e endPtr X86.jmpImm32
--      if canRet then Ret <$ writeAsm X86.ret else use retLoc
----  Reg r (Bits s) -> mkSwitch r Nothing
----  VSum (Reg r (Bits s)) datum -> mkSwitch r (Just datum)
--    x -> error $ show x
--  x -> error $ show (embed (Question <$ x))
--
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
did_LiveRegs :: Word16 -> Word16
did_LiveRegs live = trace @String (printf "%b\n" live) live

bindToAsm :: ModuleIName -> V.Vector LoadedMod -> MV.IOVector _ -> (Ptr Word8 , Int) -> Int -> Expr -> IO (Ptr Word8)
bindToAsm thisM loadedMods mb (memPtr' , memLen') bindINm expr = let
  -- Get calling convention from the function
  (argValues , retValue@(Reg X86.RAX _)) = getCallingConv expr
  liveRegsStart = complement 0 `clearBit` fromEnum X86.RSP -- All Except RSP
  liveArgs = V.foldl (\live (Reg r _) -> clearBit live (fromEnum r)) (complement 0) argValues
  rhs = getRhs (V.length argValues) expr
  startState = MkX86State
    { _memPtr = memPtr' , _memLen = memLen'
    , _modBinds = mb
    , _liveRegs = did_LiveRegs (liveArgs .&. liveRegsStart)
    , _argRegs  = did_ argValues
    }
  cgBind = genAsm argValues retValue rhs
  in do
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
