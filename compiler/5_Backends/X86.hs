module X86 where
--import Data.Bits
import Data.Binary.Put
import Data.ByteString.Lazy.Char8 (unpack)
import qualified Data.ByteString.Internal as BS (c2w) --, w2c)

import Numeric (showHex) --, showIntAtBase)

import Foreign.Ptr
--import Control.Monad.Trans.Except
--import Foreign.C.Types
--import Foreign.C.String

data Reg -- The order is vital, so fromEnum produces the right int for each register
  = RAX  -- Accumulator
  | RCX  -- Counter (Loop counters)
  | RDX  -- Data
  | RBX  -- Base / General Purpose
  | RSP  -- Current stack pointer
  | RBP  -- Previous Stack Frame Link
  | RSI  -- Source Index Pointer
  | RDI  -- Destination Index Pointer
  | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15
  | XMM0 | XMM1 | XMM2 | XMM3 | XMM4 | XMM5 | XMM6 | XMM7
  | XMM8 | XMM9 | XMM10 | XMM11 | XMM12 | XMM13 | XMM14 | XMM15
  deriving (Eq, Show , Enum)

-- Order matters again
--data Size = BYTE | WORD | DWORD | QWORD | AUTO
-- deriving (Eq , Show , Enum)
--data ArgType
-- = Reg8 | Reg16 | Reg32 | Reg64
-- | IMM8 | IMM16 | IMM32 | IMM64
-- | RegLabel8 | RegLabel16 | RegLabel32 | RegLabel64
-- | RegOffset8 | RegOffset16 | RegOffset32 | RegOffset64
-- | Label8 | Label16 | Label32 | Label64
-- | Absolute8 | Absolute16 | Absolute32 | Absolute64
-- | ScaledIdx8 | ScaledIdx16 | ScaledIdx32 | ScaledIdx64
-- | RIPRelativeIdx8 | RIPRelativeIdx16 | RIPRelativeIdx32 | RIPRelativeIdx64
-- | IMM_Auto = 240
-- | Reg_Label_Auto = 241
-- | Reg_Offset_Auto = 242
-- | Label_Auto = 243
-- | Absolute_Auto = 244
-- | Scaled_Idx_Auto = 245
-- deriving (Eq , Show , Enum)

data Val
  = I Int64      -- int
  | R Reg        -- register
  | A Word32     -- Addr
  deriving (Eq, Show)

data Instr
  = Ret
  | Mov Val Val
  | Add Val Val
  | Sub Val Val
  | Mul Val
  | IMul Val Val
  | Xor Val Val
  | Inc Val
  | Dec Val
  | Push Val
  | Pop Val
  | Call Val
  | Loop Val
  | Nop
  | Syscall
  deriving (Eq, Show)

-----------
-- Monad --
-----------
data JITMem = JITMem
 { _instrs ∷ [Instr]
 , _mach   ∷ [Word8]
 , _icount ∷ Word32
 , _memptr ∷ Word32
 , _memoff ∷ Word32
 } deriving (Eq, Show)

type X86 a = StateT JITMem (Except String) a

istate ∷ Word32 → JITMem
istate start = JITMem
  { _instrs = []
  , _icount = 0
  , _mach   = []
  , _memptr = start
  , _memoff = start
  }

emit ∷ [Word8] → X86 ()
emit i = modify $ \s → s
  { _mach = _mach s ++ i
  , _memoff = _memoff s + fromIntegral (length i)
  }

imm ∷ Integral a ⇒ a → X86 ()
imm = emit . bytes

-- Instructions
ret ∷ X86 ()
ret = emit [0xc3]

rexPre = 0x48

add ∷ Val → Val → X86 ()
add (R l) (I r) = emit [0x48 , 0x05] *> imm r
add (R l) (R r) = emit [0x48 , 0x01 , 0xc0 .|. index r `shiftL` 3 .|. index l]
add _ _ = nodef

sub ∷ Val → Val → X86 ()
sub (R l) (I r) = emit [0x48 , 0x2D] *> imm r
sub (R l) (R r) = emit [0x48 , 0x29 , 0xc0 .|. index r `shiftL` 3 .|. index l]

push ∷ Val → X86 ()
push (R l) = emit [0x50 + index l]
push _ = nodef

pop ∷ Val → X86 ()
pop (R l) = emit [0x58 + index l]
pop _ = nodef

call ∷ Val → X86 ()
call (A dst) = do
  src ← gets _memoff
  emit [0xE8]
  imm (dst - (src + 5))
call _ = nodef

mul ∷ Val → X86 ()
mul (R l) = emit [0x48 , 0xF7 , 0xE0 .|. index l]
mul _ = nodef

imul ∷ Val → Val → X86 ()
imul (R l) (I r) = emit [0x48 , 0x69 , 0xC0 .|. index l] *> imm r
imul (R l) (R r) = emit [0x48 , 0x0F , 0xAF , 0xC0 .|. index r `shiftL` 3 .|. index l]
imul _ _ = nodef

mov ∷ Val → Val → X86 ()
mov (R dst) (I src) = emit [0x48 , 0xC7 , 0xC0 .|. (index dst .&. 7)] *> imm src
mov (R dst) (A src) = emit [0x48 , 0xC7 , 0xC7] *> imm src
mov (R dst) (R src) = emit [0x48 , 0x89 , 0xC0 .|. index src `shiftL` 3 .|. index dst]
mov _ _ = nodef

nop ∷ X86 ()
nop = emit [0x90]

inc ∷ Val → X86()
inc (R dst) = emit [0x48 , 0xFF , 0xc0 + index dst]
inc _ = nodef

dec ∷ Val → X86()
dec (R dst) = emit [0x48 , 0xFF , 0xc0 + (index dst + 8)]
dec _ = nodef

loop ∷ Val → X86()
loop (A dst) = do
  emit [0xE2]
  src ← gets _memoff
  ptr ← gets _memptr
  emit [fromIntegral $ dst - src]
loop _ = nodef

syscall ∷ X86 ()
syscall = emit [0x0f , 0x05]

-- Functions
prologue ∷ X86 ()
prologue = do
  push rbp
  mov rbp rsp

epilogue ∷ X86 ()
epilogue = do
  pop rax
  mov rsp rbp
  pop rbp
  ret

-- Registers
rax , rbp , rsp , rdi , rsi , rdx , rcx ∷ Val
rax = R RAX
rbp = R RBP
rsp = R RSP
rdi = R RDI
rsi = R RSI
rdx = R RDX
rcx = R RCX

label ∷ X86 Val = A <$> gets _memoff

nodef ∷ X86 () = lift (throwE "Invalid operation")

index ∷ Reg → Word8 = fromIntegral . fromEnum

assemble ∷ Ptr a → X86 b → Either String JITMem
assemble start = runExcept . flip execStateT (istate (heapPtr start))

hex ∷ (Integral a, Show a) ⇒ a → String
hex x = showHex x ""

heapPtr ∷ Ptr a → Word32
heapPtr = fromIntegral . ptrToIntPtr

bytes ∷ Integral a ⇒ a → [Word8]
bytes x = fmap BS.c2w (unpack $ runPut $ putWord32le (fromIntegral x))
