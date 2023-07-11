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
 = Bits NBits -- can be any size and may span multiple registers / spill. (16 ymm regs = 4096 bits)
-- | Span NBits (V.Vector Int) -- offset vector to recover VBruijns
 | ProdTy ProdType
 | SumTy Int (BSM.BitSetMap AsmType) Int -- number of alts, possible alts , largest Alt
 deriving (Show , Eq)
type CallingConv = (V.Vector Value , Value)
type ProdType = (Int , BSM.BitSetMap AsmType) -- total bits needed

-- 0. pre-name the arg and return registers
-- 1. ↓ Convert to register machine, max overlap registers, rm {} and [] types, assign reg types
--    * calling convention forces retlocs; ana pushes retlocs down as far as possible when can overlap
-- 2. ↑ allocate registers|flags|stack insert call/jmp addresses
--    * Some nodes
type RName = Int -- Encode different reg types and enumerate separately
data MiniCore
  = SetLit    (Maybe Value) Literal
  | ArgReg    (Maybe Value) Int
  | NoClobber Value MiniCore
  | CallQName Bool (Maybe Value) {- tailCall -} QName [MiniCore]
  | Instr2    PrimInstr MiniCore MiniCore -- ret reg is the right one , since last to run
  | InstrImm2 PrimInstr MiniCore Literal
  | IfElse Bool MiniCore MiniCore MiniCore -- retLoc passed to rightmost instr (calls may force our hand though)
--  | Switch    RName MiniCore [Int] [MiniCore] -- scrut , register surviving , alts
  | Ret MiniCore
  deriving Show; makeBaseFunctor ''MiniCore
deriving instance Show (MiniCoreF ())
--data IRFunction = IRFunction CallingConv QName

data RegMachineState = RegMachineState
  { -- _freshReg :: Int
    _retLoc   :: Maybe Value -- Int
  }; makeLenses ''RegMachineState
-- ↓ Convert to register machine (rm {} []). re-use regs as much as possible
-- At leaves, the cata will find register names indicating how many distinct registers the sequence needs
mkRegMachineU :: Bool -> (RegMachineState , Term) -> MiniCoreF (RegMachineState , Term)
mkRegMachineU isTop (st , term) = case term of
  Top t       -> case t of -- We care about tail calls and ret-ting out of branches
    CaseB{}     -> mkRegMachineU True (st , t)
    App Var{} _ -> mkRegMachineU True (st , t)
    t       -> RetF (st , t)
  Lit l       -> SetLitF (st ^. retLoc) l
  VBruijn i   -> ArgRegF (st ^. retLoc) i -- maybe (ArgRegF i) (\r -> RenameArgF r i) (st ^. retLoc)
  -- v First branch may re-use ret-reg , second branch must find itself a new reg
  --   (calling convs are likely to cause overlap)
  -- also push down the retLoc for the lOp to use
  -- !
  App (Instr i) [lOp , rOp] -- may assume immediates are in rOp , simplifier reassociates if possible
    | Lit imm <- rOp -> InstrImm2F i (st , lOp) imm
--  | otherwise -> Instr2F i (st , lOp) (st & freshReg %~ (1+) & retLoc .~ Nothing , rOp)
    | otherwise -> Instr2F i (st & retLoc .~ Nothing , lOp) (st , rOp)
  App (Var (VQBindIndex q)) args -> let -- TODO prepare retloc for arg slots?
    st' = st & retLoc .~ Nothing
    in CallQNameF isTop (st ^. retLoc) q ((st', ) <$> args) -- TODO read calling conv!
      -- (zipWith (\i arg -> (st' & freshReg %~ (i+) , arg)) [0..] args)

  -- v Case alts are sorted by BSM , so first alt is always 0
  CaseB mkScrut _t alts Nothing | BSM.size alts == 2 , [ok , ko] <- V.toList (BSM.elems alts) -> let top = if isTop then Top else identity in -- Branches share same initial states since will run disjoint
    IfElseF isTop (st & retLoc .~ Nothing , mkScrut) (st , top ok) (st , top ko)

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

allocReg :: MkX86M X86.Reg
allocReg = liveRegs %%= \l -> if l == 0 then error "no free regs: TODO push to stack"
  else countTrailingZeros l & \r -> (toEnum r , clearBit l r)
freeReg :: X86.Reg -> MkX86M ()
freeReg r = liveRegs %= (`setBit` fromEnum r)
regIsFree :: X86.Reg -> MkX86M Bool
regIsFree r = use liveRegs <&> \live -> live `testBit` fromEnum r
getLiveRegs :: MkX86M [X86.Reg]
getLiveRegs = use liveRegs <&> \lv -> bitSet2IntList (fromIntegral (complement lv) `clearBit` fromEnum X86.RSP) <&> toEnum
-- TODO sometimes need to alloc multiple regs
allocValue ty = allocReg <&> \r -> Reg r ty
allocMReg :: AsmType -> Maybe Value -> MkX86M Value
allocMReg ty = maybe (allocValue ty) pure

-- Finally inverse the AST: @leaf: regName - argRegs = number of registers needed to compute the branch
-- There is some conflict between retLoc and argRegs
--   -> retLoc is pushed down and argReg renamed to free it quickly
--   TODO sometimes merge into a lea / 3-op xmm instruction
--mkX86F :: MiniCoreF (MkX86M X86.Reg) -> MkX86M X86.Reg
mkX86F :: MiniCoreF (MkX86M Value) -> MkX86M Value
mkX86F = \case
  SetLitF r (Fin n imm) | n <= 32 -> allocMReg (Bits 32) r >>= \r@(Reg reg (Bits rN)) ->
    r <$ writeAsm (X86.movImm32 reg (fromIntegral imm)) <* (when (rN /= n) (error $ show (n , rN)))
  ArgRegF mV i -> use argRegs <&> (V.! i) >>= \av@(Reg argReg argTy) -> case mV of
    Nothing -> pure av
    Just rv@(Reg rg retTy) | argTy == retTy -> rv <$ writeAsm (X86.movR64 rg argReg)
--RenameArgF r i -> allocReg r >>= \reg -> Reg reg rty <$ freeReg argReg <* writeAsm (X86.movR64 reg argReg)
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
    -- TODO its possible that rBranch overwrites registers from lBranch
    in mkL >>= \lv@(Reg l _) -> mkR >>= \rv@(Reg r _) -> writeAsm (x86Instr r l) *> freeReg l $> rv
--  NumInstr (IntInstr Sub)  -> v <$ writeAsm (X86.subImm32 l (fromIntegral imm))
--  PredInstr LTCmp -> VFlag ZFlag <$ writeAsm (X86.cmpImm32 l (fromIntegral imm))

  CallQNameF tailCall maybeRL q mkArgs {-| modName q == thisM-} -> use modBinds >>= \v ->
    liftIO (MV.read v (unQName q)) >>= \case
    (cc , Left{}) -> error ("forward ref: " <> showRawQName q) -- TODO topological sort?
    (cc@(argCC , retVal@(Reg retReg retTy)) , Right addr) -> do
      sequence mkArgs
      if tailCall
      then use memPtr >>= \ref -> retVal <$ writeAsm (X86.jmpImm32 (fromIntegral (minusPtr addr ref) - X86.jmpImm32Sz))
      else do
        spilledRegs <- getLiveRegs
        spilledRegs `forM` \r -> writeAsm (X86.push r)
        ref <- use memPtr
        writeAsm (X86.callImm32 (fromIntegral (minusPtr addr ref) - X86.callRelativeSz))
        -- Its possible a different arg wanted to write to RAX/our ret-conv, in which case rename our ret here
        retValue@(Reg retReg retTy) <- regIsFree retReg >>= \case
          True -> pure retVal
          False -> allocReg >>= \cp -> Reg cp retTy <$ writeAsm (X86.movR64 cp retReg)
        spilledRegs `forM` \r -> writeAsm (X86.pop64 r)
        case maybeRL of
          Just (rv@(Reg r t)) | r /= retReg -> rv <$ writeAsm (X86.movR64 r retReg)
          _                   -> pure retValue

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
-- TODO pass-down callingConvs: RName <=> X86.Reg constraints
-- So at leaves allocReg can rename collisions
mhylo :: (Monad m , Traversable f) => (f a -> m a) -> (s -> m (f s)) -> s -> m a
mhylo alg coalg c = coalg c >>= sequence . fmap (mhylo alg coalg) >>= alg

genAsm argVals retVal term = let
  start = (RegMachineState (Just retVal) , Top term)
  in -- d_ (ana (mkRegMachineU False) start :: MiniCore) $
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
  (argValues , retValue) = getCallingConv expr
  liveRegsStart = complement 0 `clearBit` fromEnum X86.RSP -- All Except RSP
  liveArgs = V.foldl (\live (Reg r _) -> clearBit live (fromEnum r)) (complement 0) argValues
  rhs = getRhs (V.length argValues) expr
  startState = MkX86State
    { _memPtr = memPtr' , _memLen = memLen'
    , _modBinds = mb
    , _liveRegs = did_LiveRegs (liveArgs .&. liveRegsStart)
    , _argRegs  = argValues
    }
  cgBind = genAsm argValues retValue rhs
  in do
  MV.modify mb (\(cc , _) -> (cc , Right memPtr')) bindINm
  (_ , st) <- cgBind `runStateT` startState
  pure (st ^. memPtr)

-- * cg a module asm and write to a ptr
-- * track symbols = offset & strName
mkAsmBindings :: ModuleIName -> V.Vector LoadedMod -> Maybe IName
  -> V.Vector (LetMeta , Bind) -> (Ptr Word8 , Int)
  -> IO (Ptr Word8 , (Word64 , [(Word64 , ByteString)])) -- return endPtr and entrypoint relative to start of .txt section
mkAsmBindings modIName loadedMods maybeMain lets (memPtr , memLen) = let
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
  mainEntry <- fromIntegral <$> case maybeMain of
    Nothing -> pure 0
    Just i  -> MV.read modBinds i <&> \(_ , Right addr) -> minusPtr addr memPtr
  pure (endPtr , (mainEntry , syms)) -- main entry is our exit syscall
