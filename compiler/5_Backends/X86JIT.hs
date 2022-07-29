{-# LANGUAGE DeriveDataTypeable, ForeignFunctionInterface, GeneralizedNewtypeDeriving #-}
module X86JIT where-- ( allocateMemory, codePtr, vecPtr , asciz, extern, getFunction, jit,)
import X86
--import System.Info (os , arch) -- arch `elem` ["x86_64" , "x86"]
import qualified Data.Vector.Storable as V
import qualified Data.Vector.Storable.Mutable as VM
import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Marshal.Utils (copyBytes)
import Foreign.Ptr
import System.Posix.DynamicLinker
import System.Posix.Types
import Unsafe.Coerce

-- MMap flags
newtype ProtOption = ProtOption CInt deriving (Eq, Show, Ord, Num, Bits)
[protNone , protExec , protWrite , protRead] = ProtOption <$> [0x0 , 0x01 , 0x02 , 0x04]
instance Semigroup ProtOption where (ProtOption a) <> (ProtOption b) = ProtOption (a .|. b)
instance Monoid ProtOption    where mempty = protNone

newtype MmapOption = MmapOption CInt deriving (Eq, Show, Ord, Num, Bits)
[mmapNone , mmapPrivate , mmapAnon] = MmapOption <$> [0x0 , 0x02 , 0x20]
instance Semigroup MmapOption where (MmapOption a) <> (MmapOption b) = MmapOption (a .|. b)
instance Monoid MmapOption    where mempty = mmapNone

----------------
-- JIT Memory --
----------------
mapAnon, mapPrivate :: MmapFlags
mapAnon = 0x20
mapPrivate = 0x02

newtype MmapFlags = MmapFlags {unMmapFlags :: CInt}
  deriving (Eq, Show, Ord, Num, Bits)

foreign import ccall "dynamic"
  mkFun :: FunPtr (IO Int) -> IO Int

getFunction :: Ptr Word8 -> IO Int
getFunction mem = do
  let fptr = unsafeCoerce mem :: FunPtr (IO Int)
  mkFun fptr

jit :: Ptr Word8 -> [Word8] -> IO (IO Int)
jit mem machCode = do
  code <- codePtr machCode
  withForeignPtr (vecPtr code) $ \ptr -> do
    {-print ptr -- Pointer to Haskell array-}
    {-print mem -- Pointer to JIT memory-}
    copyBytes mem ptr (8 * 6)
  pure (getFunction mem)

data MmapException = MmapException
  deriving (Eq, Ord, Show, Typeable)

instance Exception MmapException

foreign import ccall unsafe "sys/mman.h mmap"
  c_mmap :: Ptr () -> CSize -> ProtOption -> MmapFlags -> Fd -> COff -> IO (Ptr a)

mmap :: Ptr () -> CSize -> ProtOption -> MmapFlags -> Fd -> COff -> IO (Ptr Word8)
mmap addr len prot flags fd offset = do
  ptr <- c_mmap addr len prot flags fd offset
  when (ptr == intPtrToPtr (-1)) $ throwIO MmapException
  return ptr

codePtr :: [Word8] -> IO (VM.IOVector Word8)
codePtr = V.thaw . V.fromList

vecPtr :: Storable a => VM.MVector s a -> ForeignPtr a
vecPtr = fst . VM.unsafeToForeignPtr0

allocateMemory :: CSize -> IO (Ptr Word8)
allocateMemory size = let
  pflags = protRead .|. protWrite
  mflags = mapAnon .|. mapPrivate
  in mmap nullPtr size pflags mflags (-1) 0

asciz :: [Char] -> IO Word32
asciz str = heapPtr <$> newCString (str ++ ['\n'])

extern :: String -> IO Word32
extern name = do
  dl <- dlopen "" [RTLD_LAZY, RTLD_GLOBAL]
  fn <- dlsym dl name
  pure $ heapPtr $ castFunPtrToPtr fn

-- examples
egprintf :: Word32 -> Word32 -> X86 ()
egprintf fnptr msg = do
  push rbp
  mov rbp rsp
  mov rdi (A msg)
  call (A fnptr)
  pop rbp
  mov rax (I 0)
  ret

dump :: [Word8] -> IO ()
  = \code -> Prelude.putStrLn $ intercalate " " (hex <$> code)

testJIT :: IO () = let jitsz = 256 * 1024 in do
  fn  <- extern "printf"
  msg <- asciz "Hello"
  mem <- allocateMemory jitsz

  let jitm = assemble mem (egprintf fn msg)
  case jitm of
    Left err -> Prelude.putStrLn err
    Right jitst -> let machCode = _mach jitst in do
--    dump machCode
      fn  <- jit mem machCode
      res <- fn
      Prelude.putStrLn $ ("Result: " <> show res :: Text)
