{-# LANGUAGE DeriveDataTypeable, DerivingStrategies, ForeignFunctionInterface, GeneralizedNewtypeDeriving #-}
module X86 where
import Data.Bits
import Foreign.C.String
import Foreign.Storable
import Foreign.Ptr
import System.Posix.DynamicLinker
import Unsafe.Coerce
import qualified Data.ByteString as B
import qualified Data.ByteString.Unsafe as BSU
import System.Process
import CMMap

execJIT = False

-- Registers are encoded using 4-bit value in X.reg column. al,ax,eax,rax,st0,mmx0,xmm0,ymm0 all share same number
-- Thus all registers are numbered [0..15], the 64-bit versions are named explicitly:
-- C calling conv: return in rax , args: rdi, rsi, rdx, rcx, r8, r9 , rest on stack in rev order
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
  deriving (Eq, Show , Enum)

ccall_scratchRegs    = [RDI , RSI , RDX , RCX , R8 , R9 , R10 , R11]
ccall_calleSavedRegs = [RSP , RBP , R12 , R13 , R14 , R15]

data LinuxSyscalls = SysRead | SysWrite | SysOpen | SysClose | SysNewStat | SysNewFStat | SysNewIStat | SysPoll | SysLSeek | SysMMap | SysMProtect | SysMUnMap deriving (Eq , Show , Enum)

-- multimedia registers, also max at 15 (4-bits)
newtype XMM = XMM Word8
newtype YMM = YMM Word8

--An x86-64 instruction is max 15 bytes:
-- Legacy prefixes (1-4 bytes, optional)
-- Opcode with prefixes (1-4 bytes, required)
-- ModR/M (1 byte, if required)
-- SIB (1 byte, if required)
-- Displacement (1, 2, 4 or 8 bytes, if required)
-- Immediate (1, 2, 4 or 8 bytes, if required)

-- Opcode maps (opcode can be 1|2|3 bytes length). Some opcodes are extendable via the ModR/M.reg field
-- <op>
-- 0x0F <op>
-- 0x0F 0x38 <op>
-- 0x0F 0x3A <op>

-- VEX
-- prefix needed iff. instr has no legacy opcode | ymm registers | >3 ops | 128bit xmm destination registers (128-255) of corresponding ymm must be cleared

data Immediate = B Word8 | W Word16 | D Word32 | Q Word64 -- | X | Y | Z -- byte word dword qword xmm ymm zmm
  | DRelative Word32 -- request to subtract absolute addr of this instruction from the word32
  deriving Show

fromReg :: Reg -> Word8 = fromIntegral . fromEnum

-- Rex: request 64-bit op size (32-bit usually default)
-- rex = 0100 | W | R | X | B
-- W = request 64-bit op size (if not set may default to 64)
-- R,X,B = 1-bit extensions for (8..15) registers: MODRM.reg , SIB index , ModRM.rm
-- R,B fields extend ModRM
long , longB , longX , longW , longR :: Word8
long  = 0b0100_0000 -- simplest rex byte requesting 64-bit op size
longB = 0b0001 -- extend MODRM.rm
longX = 0b0010 -- extend SIB
longR = 0b0100 -- extend MODRM.reg
longW = 0b1000 -- request 64-bit op size

-- ModR/M , encode up to 2 operands of instr: direct register or mem address
-- fieldNames. mode , register , register/memory
-- 7..0 [2mod 3reg 3rm]
-- mod: when 0b11 , register direct addressing mode is used, else register-indirect:
-- mod0 = no displ , 01= disp8 , 10 = disp32 , 11=register
-- mod=00 , r/m = 101 means absolute (displ only) addressing
--   in 32bit / rip-relative in 64-bit , where rbp reg not used
-- mod=01 and mod=10 include an offset specified by instr displacement field
--   when r/m=101 specifies a base+offset addressing mode with rBP as base
-- reg: 3bit opcode extension | 3bit register reference: Rex.R|Vex.~R can extend 1 bit
-- rm:  3bit direct/indirect register, optional displacement. Rex.B|Vex.~B 1bit ext
mrmRegAddrMode = 0xc0 -- 11000000 -- else register-indirect + optional displacement
-- /n means setting r2 to n as a 1 operand opcode extension
mkModRM_RR dst src = B (mrmRegAddrMode .|. fromReg dst `shiftL` 3 .|. fromReg src)
-- v unset high bits
--mkModRM_rr00 dst src = B (dst `shiftL` 3 .|. src)
mkModRM_rr dst src = B (mrmRegAddrMode .|. dst .<<. 3 .|. src)
mkModRM_Dest r1 = B (mrmRegAddrMode .|. fromReg r1) -- specify destination register
mkModRM_digit n src = B (mrmRegAddrMode .|. n .<<. 3 .|. fromReg src)

-- SIB(scale index base), present whem ModR/M requests it: (mod/=11 & .r/m=100)
--   called indexed register-indirect addressing
--   0b_ss_iii_bbb = scale_index_base (scale left shifts)
--   REX.X exents iii , REX.B extends base
--   index and base encode registers => effective_addr = scale*index + base + offset
--   ! (if index=rsp , scale*index = 0) or (if modRM.mod=00 & base=rbp , base=0)
mkSIB scale index base = scale .<<. 6 .|. index .<<. 3 .|. base

ret    = [B 0xc3]
-- PUSH reg64 = 50 +rq (REX.B extension)
push r = fromReg r & \i -> if i < 8 then [B (0x50 + i)] else [B (long .|. longB) , B (0x50 + i - 8)]
pushImm8 c = [B 0x6A , B c] -- Note these things are sign extended to operating size
pushImm32 c = [B 0x68 , D c] -- push16, push32 have same opcode
pushImm64 c = [B 0x68 , D c] -- push16, push32 have same opcode
pop64 r = [B (0x58 + fromReg r)]
--pop64 r | reg <- fromReg r , reg < 8 = [long , B (0x58 + reg)] -- TODO rex
noop   = [B 0x90]
hlt    = [B 0xf4]

-- need Rex prefix to extend to 16 register set
-- TODO also can set REX.W to make default 64 bit mode
mkBinInstr opCode r l = let rI = fromReg r ; lI = fromReg l in if
  | rI < 8 -> if lI < 8 then [B opCode , mkModRM_rr rI lI] -- both < 8
              else [B (long .|. longB) , B opCode , mkModRM_rr rI (lI - 8)] -- (lI >= 8)
  | lI < 8 -> [B (long .|. longR) , B opCode , mkModRM_rr rI (lI - 8)] -- (rI >= 8)
  | True   -> [B (long .|. longR .|. longB) , B opCode , mkModRM_rr (rI - 8) (lI - 8)] -- both >= 8

inc r          = [B 0xFF , B $ 0xc0 + fromReg r] -- modR/M byte.. make clearer
dec r          = [B 0xFF , B $ 0xc0 + (fromReg r + 8)]
addReg         = mkBinInstr 0x03
subReg         = mkBinInstr 0x2B
addMem32       = mkBinInstr 0x01
add32          = mkBinInstr 0x03
xorR           = mkBinInstr 0x33
addImm32 RAX i = [B 0x05 , D i]
addImm32 r i   = [B 0x81 , mkModRM_digit 0 r , D i]
add8 r l       = mkBinInstr 0x00 r l

andImm32 RAX i = [B 0x25 , D i]
andImm32 r   i = [B 0x81 , mkModRM_digit 4 r , D i]
andImm8  RAX i = [B 0x24 , B i]
andImm8  r   i = [B 0x83 , mkModRM_digit 4 r , B i]
andR32         = mkBinInstr 0x23
-- andN is a BMI1 VEX instruction

cmpImm8 RAX ib  = [B 0x3C , B ib]
cmpImm8 r ib    = mkBinInstr 0x80 (toEnum 7) r ++ [B ib]
cmpImm32 RAX ib = [B 0x3D , D ib]
cmpImm32 r ib   = mkBinInstr 0x81 (toEnum 7) r ++ [D ib]
cmpReg8         = mkBinInstr 0x3A
cmpReg32        = mkBinInstr 0x3B

subImm32 RAX i = [B 0x2D , D i]
subImm32 r i   = [B 0x81 , mkModRM_digit 5 r , D i]

iMul64Reg r   l = B 0x0F : mkBinInstr 0xAF r l -- IMUL reg64, reg/mem64 0F AF /r
-- iDiv: Signed div: EDX:EAX / r; store the quotient in EAX and the remainder in EDX.
-- ! ie. clobbers EAX & EDX
iDiv            = mkBinInstr 0xF7 (toEnum 7)   -- IDIV reg/mem32 F7 /7

-- flags
stc = [B 0xF9]

bytesToD a b = W (b .<<. 8 .|. a) -- TODO only on Little endian..

-- set_ work on reg/mem8
mkSet_ n r = [bytesToD 0xF (90 + n) , mkModRM_digit 0 r]
[setO , setNO , setB{-B/C/NAE-} , setNB{-NB/NC/AE-} , setZ{-Z/E-} , setNZ{-NZ/NE-}
 , setBE{-BE/NA-} , setNBE{-NBE/A-} , setS , setNS , setP{-P/PE-} , setNP{-NP/PO-}
 , setL{-L/NGE-} , setNL{-NL/GE-} , setLE{-LE/NG-} , setNLE{-NLE/G-}]
 = mkSet_ <$> [0..0xF]

jmpImm8 i  = [B 0xEB , B i]
jmpImm32 i = [B 0xE9 , D i]
jmpReg r   = [B 0xFF , mkModRM_digit 4 r]

-- Jmp conditionally: 0x0F prefix then this enum occupies opcodes [0x80..0x8F]
data JmpCond = JO | JNO | JC{-jnae-} | JNC | JZ{-je-} | JNZ | JBE{-jna-} | JNBE
  | JS | JNS | JP | JNP | JL | JNL | JLE | JNLE deriving (Enum , Eq , Show)
jmpCondImm32Sz  = 6 :: Word32 -- jmps are relative to end of instructions
jmpImm32Sz      = 5 :: Word32 -- jmps are relative to end of instructions
jmpCondImm32 jmpCond i = [bytesToD 0x0F (fromIntegral (fromEnum jmpCond) + 0x80) , D i]

-- vex is usually 3 bytes, but 2 byte sometimes possible:
-- vex3 = 0xc4 | ~R , ~X , ~B , 5xmap_select | W/E , ~vvvv , L , pp
-- vex2(0xc5) implies Vex.~X=1 , Vex.~B=1 , VEX.W/E=0 & map_select = 0b00001
--   Also , nstead of W/E, the next byte has a ~R
--   0xc5 | ~R , ~vvvv , L , pp
-- * RXB are inverted extensions to MDRM.reg , SIB.index , MODRM.rm|SIB.base
-- * W/E 1bit = when set, for int instrs = use 64-bit operand ,else default (like REX.W)
--    non-int instrs => general opcode extension bit
-- * L  = 128/256 toggle
-- * pp = implied mandatory prefix. (00=None 01=0x66 10=0xF3 11=0xF2)
-- * vvvv is used in 4-op instructions: VEX.vvvv , MODR/M.reg , ModR/M.r/m and imm[7:4]
-- 2-op instrs: use ModR/M, dest in modR/M.reg ; reg/mem src in ModR/M.r/m
--   VEX.vvvv is not used and must be 0b1111
-- 3-op: VEX.vvvv counts down registers (ie. 0b1111 = 0 , 0b1110 = 1 etc..)
vex3 = B 0xc4
vex2 = B 0xc5

-- eg: C4 RXB.00001 X.src.1.01 58 /r
data VecInstrDef = VecInstrDef
  { vInstrMap :: Word8 -- 5Bits , must be [0..0b11111]
  , wideORExt :: Bool  -- for int instrs use 64-bit , Else general opcode extension bit
  , vpp       :: Word8 -- 2 bits
  , vopcode   :: Word8
--, imm       :: Immediate
  }

dvpshufb     = VecInstrDef 0b00010 False 0b01 0x00 -- c4 RXB.02 X.src1.0.01 00 /r
dvinserti128 = VecInstrDef 0b00011 False 0b01 0x38
dvpcmpeqb    = VecInstrDef 0b00001 False 0b01 0x74
dvpmovmskb   = VecInstrDef 0b00001 False 0b01 0xd7

vzeroupper = [vex2 , B 0xf8 , B 0x77]

vpshufb = vInstr3 True dvpshufb
-- v todo better imm handling
vinserti128 dst src (XMM src2) imm = vInstr3 True dvinserti128 dst src (YMM src2) <> [B imm]
vpcmpeqb    = vInstr3 True dvpcmpeqb
vpmovmskb dst = vInstr1 dvpmovmskb dst

vInstr2 idef dst src = vInstr3 True idef dst src (YMM 0) -- identity src2
vInstr1 idef dst src = vInstr2 idef (YMM (fromReg dst)) src

vInstr3 l256 idef (YMM destRaw) (YMM src) (YMM src2Raw) = let
  (dst , dstMask)   = if destRaw > 7 then (destRaw .&. 0b0111 , 0b011_11111) else (destRaw , 0xFF)
  (src2 , src2Mask) = if src2Raw > 7 then (src2Raw .&. 0b0111 , 0b110_11111) else (src2Raw , 0xFF)
  l128Mask = if l256 then 0xFF else 0b1_1111_0_11
  byteX_SRC1_L_PP = vpp idef .|. 0b1_1111_1_00 .&. l128Mask - (src .<<. 3)
  -- ! We can sometimes save a byte: vex2 implies Vex.~X=1 , Vex.~B=1 , VEX.W/E=0 & map_select = 0b00001
  in (if vInstrMap idef == 0b00001 && not (wideORExt idef) && src2Raw < 8 -- have ~R extension in vex2 mode for big dst
  then [vex2 -- in vex2 the first bit is ~R not W/E! unset first bit if dst > 7
  , B (if destRaw <= 7 then byteX_SRC1_L_PP else clearBit byteX_SRC1_L_PP 7)] -- X.src1.L.PP
  else let wExtMask = if wideORExt idef then 0xFF else 0b0_1111_1_11
  in [vex3
  , B $ 0b111_00000 .&. dstMask .&. src2Mask .|. vInstrMap idef -- RXB.map_select (vex3 extra byte)
  , B $ wExtMask .&. byteX_SRC1_L_PP                            -- X.src1.L.PP
  ]) ++ [ B (vopcode idef) , mkModRM_rr dst src2 ]  -- no matter the prefix, add opcode and ModR/M byte

-- Call-relative instr needs its addr, DRelative will be patched in
callRelativeSz = 5 :: Word32
callRelative32 dstA = [B 0xE8 , DRelative dstA] -- relative to end of call instr (just after 0xE8)
-- recall: /digit means ModRM.reg field is used as instruction-opcode extension [0..7]
callAbsolute reg = [B 0xFF , mkModRM_digit 2 reg] -- FF /2
callImm32 dstA = [B 0xE8 , D dstA]

-- Mov. (b8..bf) are only ones supporting 64-bit operand
-- +r[b|w|d|q] means add register value to hex byte on the left
-- 8: B0 +rb ib ; 16: B8 +rw iw ; 32: B8 +rd id ; 64: B8 + rq iq

-- v MOV reg64,imm64 = B8 +rq iq. (+rq not quite 1:1 with normal registers!)
movImm64 dst imm64 | d <- fromReg dst , d < 8
  = [B (0xB8 + d) , Q imm64]

movImm32 dst imm32 = [B 0xc7 , mkModRM_Dest dst , D imm32]
movzx32_8  dst = [B 0x0F , B 0xB6 , mkModRM_Dest dst]
movzx32_16 dst = [B 0x0F , B 0xB7 , mkModRM_Dest dst]
--movzx32_8  dst = [B 0x0F , B 0xBE , mkModRM_Dest dst]
--movzx32_16 dst = [B 0x0F , B 0xBF , mkModRM_Dest dst]
movsxd dst src = mkBinInstr 0x63
movDollar32 dst = [B 0xc7 , mkModRM_Dest dst , DRelative 0]
movR64 dst src = mkBinInstr 0x89 src dst -- = [B 0x89 , mkModRM_RR src dst] -- X86 flips src and dest
(movs8 , movs32) = (B 0xA4 , B 0xA5) -- move at RSI to RDI

lea dst srcMem = [B 0x8D , mkModRM_RR srcMem dst] -- 8D \r (Can request SIB byte!)

interrupt = B 0xCD
syscall = [B 0x0f , B 0x05]

heapPtr :: Ptr a -> Word32
heapPtr = fromIntegral . ptrToIntPtr

type Prog = [[Immediate]]
mkAsm :: Int -> Ptr Word8 -> [Immediate] -> IO Int
mkAsm len mem prog = let
  go i = \case
    B c -> i + 1 <$ pokeByteOff mem i c
    W w -> i + 2 <$ pokeByteOff mem i w
    D d -> i + 4 <$ pokeByteOff mem i d
    Q q -> i + 8 <$ pokeByteOff mem i q
    DRelative d -> i + 4 <$ pokeByteOff mem i (d - heapPtr mem - 4 - fromIntegral i)
  in foldM go 0 prog -- >>= \i -> (i + 1) <$ pokeByteOff mem i '\0'
mkAsm' l mem prog = mkAsm l mem prog <&> \len -> plusPtr mem len

---------
-- JIT --
---------
-- Cast executable code to _ -> Int
foreign import ccall "dynamic"
  mkFun :: FunPtr (IO Int) -> IO Int
getFunction :: Ptr Word8 -> IO Int
getFunction mem = mkFun (unsafeCoerce mem :: FunPtr (IO Int))

runJIT :: Prog -> IO Int
runJIT prog = let
  jitsz = 0x40000 -- 256 * 1024
  iJitsz = fromIntegral jitsz :: Int
  in do
  ptrExecutable <- mmap nullPtr jitsz (protRead .|. protWrite .|. protExec)
    (mmapAnon .|. mmapPrivate) (-1) 0
  len <- mkAsm iJitsz ptrExecutable (concat prog)

  -- objdump disassembly, TODO Should memcpy ptr (copyBytes : Ptr -> Ptr -> Int -> IO ())
  bs <- BSU.unsafePackCStringLen (castPtr ptrExecutable , len)
  B.writeFile "/tmp/instrs.bin" bs -- ptrExecutable
  readProcess "objdump" ["-D", "-b" , "binary" , "-M" , "intel" , "-m" , "i386:x86-64" , "/tmp/instrs.bin"] ""
    >>= putStrLn

  res <- if execJIT then getFunction ptrExecutable else pure (-1) -- an (IO Int)
  c_munmap ptrExecutable jitsz >>= \case
    -1 -> error "failed to munmap ?"
    _  -> pure ()
  pure res

extern :: String -> IO Word32
extern name = do
  dl <- dlopen "" [RTLD_NOW, RTLD_GLOBAL]
  heapPtr . castFunPtrToPtr <$> dlsym dl name

callPuts = do
  cstr <- newCString "Hello\n\0"
  fn   <- extern "printf"
--let fn = fromIntegral (ptrToIntPtr c_puts)
  pure
    [ movImm32 RDI (heapPtr cstr)
    , callRelative32 fn --  , movImm32 RAX fn , callAbsolute RAX
    , xorR RAX RAX
    , ret
    ]

readSysCall = 
  [ subImm32 RSP 16
  , movImm32 RAX (fromIntegral (fromEnum SysRead))
  , movImm32 RDI 0 -- stdin fd
  , movR64 RSI RSP
  , movImm32 RDX 4 -- 4 bytes
  , syscall
  , addImm32 RSP 16
  , ret
  ]

exit42SysCall = [ movImm32 RAX 60 , movImm32 RDI 42 , syscall ]
exitSysCall = [ movR64 RDI RAX , movImm32 RAX 60{-SysExit-} , syscall ]

writeSysCall =
  [ movImm32 RAX (fromIntegral (fromEnum SysWrite)) -- movImm64 RAX 1 -- write syscall
  , movImm32 RDI 1 -- stdout fd
  , pushImm32 0x6f6c6548 -- "helo"
  , movR64 RSI RSP
  , movImm32 RDX 4 -- msg len
  , syscall
  , pop64 RDI
  ]
  ++ exitSysCall

testVecs =
   [ vinserti128 (YMM 0) (YMM 0) (XMM 1) 0x1
   , vpshufb (YMM 8) (YMM 14) (YMM 10)
   , vpcmpeqb (YMM 15) (YMM 1) (YMM 0)
   , vpmovmskb RAX (YMM 0) -- will actually be EAX , should type enforce this
   , vzeroupper
   , ret
   ]

--testJIT = runJIT writeSysCall
--testJIT = callPuts >>= runJIT
--testJIT = pure testVecs >>= runJIT
testJIT = runJIT writeSysCall
