{-# LANGUAGE DeriveDataTypeable, DerivingStrategies, ForeignFunctionInterface, GeneralizedNewtypeDeriving #-}
module CMMap where
import Foreign.C.Types
import Foreign.Ptr
import System.Posix.Types

newtype ProtOption = ProtOption CInt deriving newtype (Eq, Show, Ord, Num, Bits)
[protNone , protExec , protWrite , protRead] = ProtOption <$> [0x0 , 0x01 , 0x02 , 0x04]
newtype MmapFlags = MmapOption CInt deriving newtype (Eq, Show, Ord, Num, Bits)
[mmapNone , mmapPrivate , mmapAnon] = MmapOption <$> [0x0 , 0x02 , 0x20]

foreign import ccall unsafe "sys/mman.h mmap"
  c_mmap :: Ptr () -> CSize -> ProtOption -> MmapFlags -> Fd -> COff -> IO (Ptr a)
foreign import ccall unsafe "sys/mman.h munmap"
  c_munmap :: Ptr a -> CSize -> IO Fd
mmap :: Ptr () -> CSize -> ProtOption -> MmapFlags -> Fd -> COff -> IO (Ptr Word8)
mmap addr len prot flags fd offset = do
  ptr <- c_mmap addr len prot flags fd offset
  ptr <$ when (ptr == intPtrToPtr (-1)) (error "couldn't mmap for JIT")

foreign import ccall unsafe "stdio.h puts"
--  c_puts :: Ptr () -> IO Int
  c_puts :: Ptr Word8

