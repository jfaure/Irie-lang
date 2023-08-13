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
import Control.Monad.Trans.Cont

-- Reg optimisation:
-- ? Some functions may as well leave (some) args untouched in input registers
-- ? Full program reg convention desired check

-- Prim -> X86
getX86NumInstr = \case
  IntInstr Mul -> X86.iMul64Reg
  IntInstr Add -> X86.addReg
  IntInstr Sub -> X86.subReg
  x -> error $ show x
getX86InstrImm32 = \case
  NumInstr (IntInstr Add) -> Just X86.addImm32
  NumInstr (IntInstr Sub) -> Just X86.subImm32
  _ -> Nothing
getX86JmpPred = \case
  LTCmp -> X86.JL ; GECmp -> X86.JNL ; LECmp -> X86.JLE ; GTCmp -> X86.JNLE
  EQCmp -> X86.JZ ; NEQCmp -> X86.JNZ

-----------------------------------
-- Reg/Mem <=> VBruijn isomorphisms
-----------------------------------
-- hylo:
-- 1. ↓ Set forced registers (calling conv.) & build rpn exprs
-- 2. ↑ Emit X86 instructions: Reg/Mem assignments , track Reg/Mem state

type NBits = Int
data AsmType
 = Bits NBits -- Any size; multiple registers / spill. (16 ymm regs = 4096 bits)
 | ProdTy ProdType
 | SumTy SumType
 deriving (Show , Eq)

type CallingConv = (V.Vector Value , Value)
type ProdType = (Int , BSM.BitSetMap AsmType) -- total bits needed
type SumType = (Int , BSM.BitSetMap AsmType , Int) -- num alts, alts , largest Alt

data Value
  = Reg X86.Reg AsmType -- can index all registers incl xmm etc, based on asmtype
  | VProd (V.Vector Value) ProdType
  | VJmpCond X86.JmpCond -- Use set[le..] to get flag into a register
  | StackLoc Int AsmType
  deriving (Show , Eq)

data RetNode
  = SetLit    Literal
  | ArgReg    Int
  | CallQName Bool QName [RetNode] -- isTailCall

  -- 1. running RPN may free registers.
  -- 2. Use RAX as much as possible. (shorter instrs)
  -- 3. Must respect calling conventions when computing the stack
  -- 4. Must End in retloc (unless ifElse cond)
  -- inp stack (forced calling convs) & rpn instructions (dependency chain)
  | RPN [RetNode] [PrimInstr] -- [Either PrimInstr ( , PrimInstr)]

  | IfElse Bool RetNode RetNode RetNode
  | Ret Value RetNode
  deriving Show; makeBaseFunctor ''RetNode
instance Show (RetNodeF ())

-- a foldl on semi-flattened term tree (only flatten AppInstr nodes)
-- Point is to clarify separation of calling-convention nodes and nodes that don't care
-- Also the tree is now in asm order, with nodes executed first: In fact the '++' indicates overlappable instrs
-- ! regs always end up in lOp
mkRPN :: ([Term] , [PrimInstr]) -> [Term] -> ([Term] , [PrimInstr])
mkRPN acc [] = acc
mkRPN (as , ai) (term : argsR) = case term of
  -- vv TODO mark overlappable instruction start (instead of ++)
--App (Instr i) [l , r@Lit{}] -> mkRPN (as , i : ai) (argsR ++ argsL)
  App (Instr i) argsL -> mkRPN (as , i : ai) (argsR ++ argsL)
  x -> mkRPN (x : as , ai) argsR

type RegMachineState = ()
mkRegMachineU :: _ -> _ -> Bool -> (RegMachineState , Term)
  -> RetNodeF (RegMachineState , Term)
mkRegMachineU argVals retVal isTop (st , term) = case term of
  Top t       -> case t of -- We care about tail calls and ret-ting out of branches
    CaseB{}     -> mkRegMachineU argVals retVal True (st , t)
    App Var{} _ -> mkRegMachineU argVals retVal True (st , t)
    t       -> RetF retVal (st , t)
  Lit l       -> SetLitF l
  VBruijn i   -> ArgRegF i

  App (Instr i) args -> mkRPN ([] , [i]) args & \(as , ai) -> RPNF ((st,) <$> as) ai
  App (Var (VQBindIndex q)) args -> let -- TODO prepare retloc for arg slots?
    in CallQNameF isTop q ((st, ) <$> args) -- TODO read calling conv!

  -- v Case alts are sorted by BSM , so first alt is always 0
  CaseB mkScrut _t alts Nothing | BSM.size alts == 2 , [ok , ko] <- V.toList (BSM.elems alts) -> let
    top = if isTop then Top else identity -- Branches share initial state but run disjoint
    in IfElseF isTop (st , mkScrut) (st , top ok) (st , top ko)

  x -> error $ show x

-----------
-- ↑ Gen asm: Allocate reg/mem , commit to x86 (exact jmp/call addresses)
-----------
-- * in/out regs are predetermined by calling conv.
-- * scruts & RPN intermediates are free to choose.
data MkX86State = MkX86State
  { _memPtr   :: Ptr Word8
  , _memLen   :: Int
  , _modBinds :: MV.IOVector (CallingConv , Either [Word32] (Ptr Word8))

  , _liveRegs :: Word16 -- bitset
  , _argRegs  :: V.Vector Value

--  , _callingConv :: (Int , V.Vector Int)
--  , _namedRegs   :: MV.IOVector Value
  }; makeLenses ''MkX86State

type MkX86M = StateT MkX86State IO
svState = use liveRegs :: MkX86M _
restoreState live = liveRegs .= live
writeAsm :: [X86.Immediate] -> MkX86M ()
writeAsm prog = use memPtr >>= \ptr -> use memLen >>= \len ->
  liftIO (X86.mkAsm len ptr prog) >>= \wroteLen -> memPtr %= (`plusPtr` wroteLen)
writeAsmAt ptr prog = liftIO (X86.mkAsm 15 {-max len for an instruction-} ptr prog)

freeReg :: X86.Reg -> MkX86M ()
freeReg r = liveRegs %= (`setBit` fromEnum r)
allocReg :: MkX86M X86.Reg
allocReg = liveRegs %%= \l -> if l == 0 then error "no free regs: TODO push to stack"
  else countTrailingZeros l & \r -> (toEnum r , clearBit l r)
getLiveRegs :: MkX86M [X86.Reg]
getLiveRegs = use liveRegs <&> \lv ->
  bitSet2IntList (fromIntegral (complement lv) `clearBit` fromEnum X86.RSP) <&> toEnum

mkX86F :: RetNodeF (MkX86M Value) -> MkX86M Value
mkX86F = \case
  RPNF (s : stack) instrs -> s >>= \seed -> let
    go (val , next : stack) instr = next >>= \lVal -> (,stack) <$> case val of
      rVal@(Reg r _) -> case lVal of
        (Reg l _) -> case instr of
          NumInstr (PredInstr pI) -> freeReg r *> freeReg l *>
            writeAsm (X86.cmpReg32 l r) $> VJmpCond (getX86JmpPred pI)
          NumInstr nI  -> freeReg r *> writeAsm (getX86NumInstr nI l r) $> lVal
    -- stack must be fully used
    in foldM go (seed , stack) instrs <&> \(val , []) -> val

  ArgRegF i -> use argRegs <&> (V.! i)
  SetLitF (Fin 32 imm) -> allocReg >>= \r -> Reg r (Bits 32)
    <$ writeAsm (X86.movImm32 r (fromIntegral imm))

  -- Preserve & rename registers
  CallQNameF tailCall q mkArgs {-| modName q == thisM-} -> use modBinds >>= \v ->
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
        -- Its possible a different arg wanted to write to RAX/our ret-conv
        let retValue@(Reg retReg retTy) = retVal
        reverse spilledRegs `forM` \r -> writeAsm (X86.pop64 r)
        pure retValue

  IfElseF canRet cond ok ko -> let
    patchLabel jmpSz comeFrom ref jmpTy = writeAsmAt comeFrom
      (X86.jmpCondImm32 jmpTy (fromIntegral (minusPtr ref comeFrom) - jmpSz))
    patchJmp comeFrom ref = writeAsmAt comeFrom (X86.jmpImm32 (fromIntegral (minusPtr ref comeFrom) - X86.jmpImm32Sz))
    in do
    VJmpCond jmpCond <- cond
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
    when (okRet /= koRet) (traceM $ show (okRet , koRet))
    pure okRet

  RetF ret@(Reg retLoc _) r -> r >>= \(Reg v _) -> ret <$
    (if v == retLoc then pure () else writeAsm (X86.movR64 retLoc v)) <* writeAsm X86.ret
  x -> error $ show (() <$ x)

genAsm :: V.Vector CallingConv -> V.Vector Value -> Value -> Term -> MkX86M Value
genAsm ccs argVals retVal term = d_ (argVals , retVal) $ let
  start = (() , Top term) -- (RegMachineState (RetLoc retVal) ccs , Top term)
  in d_ (ana (mkRegMachineU argVals retVal False) start :: RetNode) $
    hylo mkX86F (mkRegMachineU argVals retVal False) start

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
      in SumTy (BSM.size prod , prod , maxSz)
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
--  SumTy nAlts prod sz -> Prelude.uncons freeRegs & \(Just (tagReg , regs')) -> Prelude.uncons regs' &
--    \(Just (dataReg , cdr)) -> let value = VSum (Reg tagReg (Bits (sizeOfTagBits nAlts))) (Reg dataReg (Bits sz))
--      in (value , (argTys , cdr))
    x -> error $ show x
  allocArg ([] , _) = error "impossible"

  allocArgs = V.unfoldrExactN nArgs allocArg (reverse argTys , X86.ccall_scratchRegs)
  allocRet  = fst $ allocArg ([retTy] , X86.RAX : X86.ccall_scratchRegs)
  in (allocArgs , allocRet)

asmSizeOf :: AsmType -> NBits
asmSizeOf = \case
  Bits n -> n
  ProdTy (p , _) -> p
  SumTy (n , p , sz) -> sizeOfTagBits n + sz -- sizeof gets number of bytes in an int
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

bindToAsm :: ModuleIName -> V.Vector LoadedMod -> MV.IOVector (CallingConv, Either [Word32] (Ptr Word8)) -> V.Vector CallingConv -> (Ptr Word8 , Int) -> Int -> Expr -> IO (Ptr Word8)
bindToAsm thisM loadedMods mb ccs (memPtr' , memLen') bindINm expr = let
  -- Get calling convention from the function
  (argValues , retValue) = getCallingConv expr
  liveRegsStart = complement 0 `clearBit` fromEnum X86.RSP -- All Except RSP
  liveArgs = V.foldl (\live (Reg r _) -> clearBit live (fromEnum r)) (complement 0) argValues
  rhs = getRhs (V.length argValues) expr
  startState = MkX86State
    { _memPtr = memPtr' , _memLen = memLen'
    , _modBinds = mb
    , _liveRegs = liveArgs .&. liveRegsStart -- & did_LiveRegs
    , _argRegs  = argValues
    }
  cgBind = genAsm ccs argValues retValue rhs
  in do
  MV.modify mb (\(cc , _) -> (cc , Right memPtr')) bindINm
  (_ , st) <- cgBind `runStateT` startState
  pure (st ^. memPtr)

-- * cg a module asm and write to a ptr
-- * track symbols = offset & strName
mkAsmBindings :: ModuleIName -> V.Vector LoadedMod -> Maybe IName
  -> V.Vector (LetMeta , Bind) -> (Ptr Word8 , Int)
  -> IO (Ptr Word8 , (Word64 , [(Word64 , ByteString)])) -- endPtr and entrypoint relative to start of .txt section
mkAsmBindings modIName loadedMods maybeMain lets (memPtr , memLen) = let
  -- sequentially write out all functions & collect their offsets for strtable and calls
  appendBind modBinds (ptr , offs) (lm , bind) = let
    bindQName = (letBindIndex lm) & \(VQBindIndex q) -> q
    nm = lookupBindName loadedMods (modName bindQName) (unQName bindQName)
    in case bind of
    BindOK opt rhs -> bindToAsm modIName loadedMods modBinds ccs (ptr , memLen) (unQName bindQName) rhs -- TODO memlen
      <&> \endPtr -> (endPtr , maybe offs (\nm -> (fromIntegral (minusPtr ptr memPtr) , encodeUtf8 nm) : offs) nm)
    b -> error $ show b
  ccs = lets <&> \(_lm , (BindOK _ rhs)) -> getCallingConv rhs
  in do
--modBinds <- MV.replicate (V.length lets) (Left [])
  modBinds <- V.unsafeThaw $ ccs <&> (, Left[])
  entryEndPtr <- X86.mkAsm' memLen memPtr (concat X86.exitSysCall)
  let entrySym = [(0 , "start")]
  (endPtr , syms) <- foldM (appendBind modBinds) (entryEndPtr , entrySym) lets
  mainEntry <- fromIntegral <$> case maybeMain of
    Nothing -> pure 0
    Just i  -> MV.read modBinds i <&> \(_ , Right addr) -> minusPtr addr memPtr
  pure (endPtr , (mainEntry , syms)) -- main entry is our exit syscall
