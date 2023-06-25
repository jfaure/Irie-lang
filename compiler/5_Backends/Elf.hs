{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
{-# OPTIONS_GHC -fplugin=Foreign.Storable.Generic.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt=Foreign.Storable.Generic.Plugin:-v1 #-}
module Elf where
import Data.Bits
import Data.IORef
import Foreign.Storable.Generic
import System.IO.MMap
import qualified System.IO as SIO
import Unsafe.Coerce
import qualified Data.ByteString as B
import qualified Data.ByteString.Unsafe as BSU
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector.Algorithms.Heap as VU
import Foreign.C.Types
import Foreign.C.String
import Foreign.Ptr
import Foreign.Marshal.Utils
import CMMap
import System.Process
import qualified X86

-- Elf files are a spaghetti of relative pointers

-- Dynamic linking (3 mandatory progheaders , 8 dyn sections (+ DT_NULL)):
-- 1. kernel looks at PT_INTERP in prog segment header
-- 2. linker reads dyn section from prog-segment table to find reloc table
-- 3. reloc table has a relative address to symbol in symbol table
-- 4. symbol table has entry in string table
-- 5. linker looks through shared object libs for sym name
-- 6. adjust lib-symbol val to our process and relative to address in reloc table

-- All 32-bit fields must be DWord aligned
-- easiest way is to move all alignment agnostic sections to the end
type ElfN_Addr = Word64 -- TODO support 32 bit?
type ElfN_Off  = Word64
data Elf = Elf
  { e_magic     :: Word32 -- 4 * magic bytes: DWord 1179403647
  , m_class     :: Word8
  , m_data      :: Word8
  , m_version   :: Word8
  , m_osabi     :: Word8
  , e_ident1    :: Word64 -- abi version , padding *7
  , e_type      :: Word16
  , e_machine   :: Word16
  , e_version   :: Word32
  , e_entry     :: ElfN_Addr
  , e_phoff     :: ElfN_Off -- pheaders tells OS how to map everythin}g
  , e_shoff     :: ElfN_Off
  , e_flags     :: Word32
  , e_ehsize    :: Word16
  , e_phentsize :: Word16
  , e_phnum     :: Word16
  , e_shentsize :: Word16
  , e_shnum     :: Word16
  , e_shstrndx  :: Word16
  } deriving (Show, Read, Generic, GStorable)

-- zero except for elf-magic and versions (all set 1), and phdr/shdr sizes
zeroElf = (Elf 1179403647 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
  { e_version = 1 , m_version = 1 , e_phentsize = fromIntegral pHdrSz , e_shentsize = fromIntegral sHdrSz }
elfHdrSz = sizeOf zeroElf

-- generally, remains to set e_type , maybe phoffphentsz,phnum,entry,shentsize,snhum,shoff
-- usually, phoff starts right after elf header, shoff at end of file
elf64x86Template = zeroElf
  { m_class   = 2 -- 64 bit
  , m_data    = 1 -- little endian
  , e_machine = 62 -- AMD x86-64
  , e_ehsize  = fromIntegral elfHdrSz
  }

type WordXX = Word64
data Phdr = Phdr
  { pType   :: Word32 -- PType: loadable | dynamic | interp etc
  , pFlags  :: Word32 -- .|. read/write/exec flags (pfR,pfW,pfX)
  , pOffset :: ElfN_Off -- offset from file beginning to segment described
  , pvaddr  :: ElfN_Addr
  , ppaddr  :: ElfN_Addr -- irrelevant on virtual memory, BSD requries 0
  , pfilesz :: Word64 -- number of bytes of segment, can be 0
  , pmemsz  :: Word64 -- number of bytes in memory of segment, can be 0
  , palign  :: Word64 -- 0|1 means no alignement required, else must be +power 2
  } deriving (Show, Read, Generic, GStorable)
data PType = PT_NULL | PT_LOAD | PT_DYNAMIC | PT_INTERP | PT_NOTE | PT_SHLIB | PT_PHDR | PT_TLS deriving Enum
(pfR , pfW , pfX) = (4 , 2 , 1)

data Elf64_Shdr = Elf64_Shdr
  { sName      :: Word32  -- ^ Section name
  , sType      :: Word32  -- ^ Section type
  , sFlags     :: WordXX  -- ^ Section attributes
  , sAddr      :: WordXX  -- ^ Virtual address in memory
  , sOffset    :: WordXX  -- ^ Offset in file
  , sSize      :: WordXX  -- ^ Size of section
  , sLink      :: Word32  -- ^ Link to other section
  , sInfo      :: Word32  -- ^ Miscellaneous information
  , sAddrAlign :: WordXX  -- ^ Address alignment boundary
  , sEntSize   :: WordXX  -- ^ Size of entries, if section has table
  } deriving (Show, Read, Generic, GStorable)
emptySHdr = Phdr 0 0 0 0 0 0 0 0
sHdrSz = sizeOf emptyPHdr

-- Symbols: describe their types, incl. offset into string table
data Elf64_Sym = Elf64_Sym
  { stName  :: Word32  -- ^ Symbol name (string table offset to Cstring)
  , stInfo  :: Word8   -- ^ STB , STT (Type , Binding) attributes
  , stOther :: Word8   -- ^ Reserved, set 0
  , stShNdx :: Word16  -- ^ Section table index to which this symbol belongs
  , stValue :: WordXX  -- ^ Symbol value
  , stSize  :: WordXX  -- ^ Size of object (0 for extern symbol)
  } deriving (Show, Read, Generic, GStorable)
data STT = STT_NOTYPE | STT_OBJECT | STT_FUNC | STT_SECTION | STT_FILE | STT_COMMON | STT_TLS deriving Enum
data STB = STB_LOCAL | STB_GLOBAL | STB_WEAK deriving Enum
mkSTInfo :: STB -> STT -> Word8
mkSTInfo b t = fromIntegral (fromEnum b) .<<. 4 .|. fromIntegral (fromEnum t)
emptyElf64_Sym = Elf64_Sym 0 0 0 0 0 0 -- should set at minimum info and stName
elf64_SymSz = sizeOf emptyElf64_Sym

-- R_386_32: direct insertion of sym value: obtain ptr to objects
-- R_386_PC32: relative to reloc address
-- R_AMD64_JUMP_SLOT, a word64 absolute address
data RelType = R_AMD64_NONE | R_AMD64_64 | R_AMD64_PC32 | R_AMD64_GOT32 | R_AMD64_PLT32 | R_AMD64_COPY | R_AMD64_GLOB_DAT | R_AMD64_JUMP_SLOT | R_AMD64_RELATIVE | R_AMD64_GOTPCREL | R_AMD64_32 | R_AMD64_32S | R_AMD64_16| R_AMD64_PC16 | R_AMD64_8 | R_AMD64_PC8 deriving Enum

data Elf64_Rel = Elf64_Rel
  { relaOffset :: WordXX -- ^ Address at which to apply relocation
  -- for relocatable file, byte offset from beginning of section to addr
  -- for exectuable/shared obj, virtual address
  , relaInfo   :: Word64 -- ^ reloc type & index to sym table
-- , relaAddend :: Word64 -- RelA tables are a different kind with extra offset
  } deriving (Show, Read, Generic, GStorable)
relSz = sizeOf (Elf64_Rel 0 0)

mkRInfo :: Word32 -> RelType -> Word64
mkRInfo sym ty = fromIntegral sym .<<. 32 .|. fromIntegral (fromEnum ty)

-- Dyn section is a map: [(DT_TAG , Ptr)]
data Elf64_Dyn = Elf64_Dyn
  { d_tag :: Word64 -- __s64
  , d_val :: Word64 -- __u64
  } deriving (Show, Read, Generic, GStorable)
emptyDyn = Elf64_Dyn 0 0

-- There are more, but they are assigned non-enumerable numbers
data DT_TAG = DT_NULL | DT_NEEDED | DT_PLTRELSZ | DT_PLTGOT | DT_HASH | DT_STRTAB | DT_SYMTAB | DT_RELA | DT_RELASZ | DT_RELAENT | DT_STRSZ | DT_SYMENT | DT_INIT | DT_FINI | DT_SONAME | DT_RPATH | DT_SYMBOLIC | DT_REL | DT_RELSZ | DT_RELENT | DT_PLTREL | DT_DEBUG | DT_TEXTREL | DT_JMPREL deriving Enum

-- * DT_Needed: can point to shared object lib
-- * hash table (use elfHash function). also has number of syms
-- lookup bucket array % nbuckets , else loop index in the chain array
-- Layout is:
--   Hashheader
--   nBuckets * Word32 -- buckets
--   nChains  * Word32 -- each chain starts at bucket[hash % nBuckets]
-- ! nChains == number of sym table entries
-- ! each chain starts with STN_UNDEF '0'
data HashHeader = HashHeader
  { hnBuckets :: Word32
  , hnSymbols :: Word32
  } deriving (Show, Read, Generic, GStorable)
hashHdrSz = sizeOf (HashHeader 0 0)

-- syms are name -> hash
-- lookup str = elfHash str % nBuckets & \h -> if strMatch bucket[h] then h
--   else deref chains until found starting at chain[h]
--   chain ends at any x where chain[x] == 0
-- eg. 1 2 1 0 0 = 1 bucket , 2 syms , bucket1 hashes to symbol 1 , null symbol , end of single chain
mkHash :: Word32 -> VU.Vector Word32 -> (HashHeader , [Word32] , V.Vector Word32)
mkHash nBuckets syms = runST $ do
  chains <- MV.new (VU.length syms)
  hashes <- VU.unsafeThaw (VU.indexed $ VU.map (\s -> mod s nBuckets) syms)
  VU.sortBy (on compare snd) hashes
  hashV <- VU.unsafeFreeze hashes  -- :: VU.Vector (Int , Word32) -- eg: [ (5 , h0 , 2 , h0 , 6 , h1 , 1 , h1) ]
  let buildVec acc@(prev , switches) (idx , hash) = if prev == hash
        then acc <$ MV.write chains idx prev -- prev ?!!
        else (hash , fromIntegral (idx + 1) : switches) <$ MV.write chains idx 0
  (_ , buckets) <- VU.uncons hashV & \(Just ((i0 , h0) , cdr)) ->
    MV.write chains i0 0 -- 0 ?!!
    *> VU.foldM buildVec (h0 , [fromIntegral i0 + 1]) cdr
  chainsV <- V.unsafeFreeze chains
  pure ( HashHeader nBuckets (fromIntegral $ VU.length syms)
       , buckets -- str Name pointed to by bucket (first str to hash%nBuckets to this bucket)
       , chainsV
       )

-- DT_HASH uses this
-- DT_GNU_HASH is better (loaders are ~50% faster), although slightly more complicated
elfHash :: ByteString -> Word32
elfHash str = (\fn -> B.foldl fn 0 str) $ \acc c -> let
  h = (acc .<<. 4) + fromIntegral c
  g = h .&. 0xf0000000
  in (if g /= 0 then xor h (g .>>. 24) else h) .&. complement g

-- same as saved in e_ehsize
elfSz32 = 0x34
elfSz64 = 0x40
-- Symbol table
-- reloc table

data ET = ET_NONE | ET_REL | ET_EXEC | ET_DYN | ET_CORE deriving Enum

emptyPHdr = Phdr 0 0 0 0 0 0 0 0
pHdrSz = sizeOf emptyPHdr

-- interp pheader, followed directly by null terminated linker absolute path
-- ptr is the start of current section
-- sz and off refer to the section this header describes, off is relative to filePtr, the start of the file
mkPHdr ty pflags sz off = Phdr
  { pType = fromIntegral (fromEnum ty)
  , pFlags = pflags
  , pOffset = off
  , pvaddr  = {-filePtr +-} off , ppaddr  = off -- filePtr + off
  , pfilesz = sz , pmemsz = sz
  , palign  = 0 }

--push :: Ptr a -> a -> IO (Ptr a)
push ptr rel = plusPtr ptr (sizeOf rel) <$ poke ptr rel
pushDWord ptr (rel :: Word32) = plusPtr ptr (sizeOf rel) <$ poke ptr rel

writeDynTab :: Ptr Word8 -> [Elf64_Dyn]{-[(DT_TAG , offset)]-} -> IO (Ptr Word8)
writeDynTab mem dyns = let
  go :: _ -> Elf64_Dyn -> _
  go ptr dyn = plusPtr ptr (sizeOf emptyDyn) <$ poke ptr dyn
  in castPtr <$> V.foldM go (castPtr mem) (V.fromList dyns)

writeStrTab :: Ptr Word8 -> V.Vector ByteString -> IO (Ptr Word8)
writeStrTab ptr strs = let
  go acc bs = let blen = B.length bs in do
    BSU.unsafeUseAsCString bs $ \cstr -> copyBytes acc (castPtr cstr) blen
    pokeByteOff acc blen (0 :: Word8)
    pure (plusPtr acc (blen + 1)) 
  in poke ptr (0 :: Word8) *> V.foldM go ptr strs

writeHashTab :: Ptr Word8 -> (HashHeader , [Word32] , V.Vector Word32) -> IO (Ptr Word8)
writeHashTab mem' (hashHdr , hashBuckets , hashChains) = let mem = castPtr mem' in do
  bucketPtr <- plusPtr mem hashHdrSz <$ poke mem hashHdr
  chainPtr  <- foldM pushDWord bucketPtr hashBuckets
  castPtr <$> V.foldM pushDWord (castPtr chainPtr) hashChains

-- v Must start with zeroed symbol
-- strNames are offsets into the symbol table
writeSymTab :: Ptr Word8 -> V.Vector Elf64_Sym -> IO (Ptr Word8)
writeSymTab mem' symVec = let
  mem = castPtr mem'
  go ptr sym = plusPtr mem elf64_SymSz <$ poke ptr sym
  in poke mem emptyElf64_Sym
  *> V.foldM go (plusPtr mem elf64_SymSz) symVec
  <&> castPtr

-- nHashBuckets should be >0 , <= length extSymbols
-- RelTab contains all addresses where a relocation needs to be inserted , + index into sym table
-- ! DynSection DT_NEEDED library names are strtab offsets (DT_STRTab key)
-- TODO mk PIE (ET_DYN instead of ET_EXEC)
mkDynElf :: Ptr Word8 -> _ -> Word32 -> ByteString -> Int -> V.Vector ByteString -> V.Vector Elf64_Rel -> X86.Prog -> IO Int
mkDynElf ptr memSz nHashBuckets interp libcName extSymbols relTab progText = let
  -- calc sizes , then can write directly to mem
  nExterns = V.length extSymbols
  strTabOffs = V.scanl (\acc bs -> acc + B.length bs + 1) 1 extSymbols -- account for null bytes (incl start null)
  strtabSz = V.last strTabOffs
  symbols = let -- symbol stNames index the strtab
    mkSym i = emptyElf64_Sym { stName = fromIntegral (strTabOffs V.! i) , stInfo = mkSTInfo STB_GLOBAL STT_FUNC }
    in V.generate (V.length extSymbols {- drop last scanl offset -}) mkSym 
  symTabSz = (1 + nExterns) * elf64_SymSz -- Must start with 0s?

  hashedSyms = VU.generate (V.length extSymbols) $ \i -> elfHash (extSymbols V.! i)
  hashInfo@(hashHdr , hashBuckets , hashChains) = mkHash nHashBuckets hashedSyms
  hashLen = hashHdrSz + 4 * (length hashBuckets + V.length hashChains) -- same as symbol count
  interpsz = fromIntegral (B.length interp)

  -- ! set this in advance of knowing dynTab
  dynTabSz = length dynTab{-9-} * sizeOf (Elf64_Dyn 0 0)

  -- This is the order we layout the headers contiguously, thus offsets are a scanl
  [eHdrOff , pInterpOff , pLoadOff , pDynOff , hashOff , symTabOff , relOff , dynOff , interpOff , strTabOff , textOff ]
    = scanl (+) 0 [fromIntegral elfHdrSz , fromIntegral pHdrSz , fromIntegral pHdrSz , fromIntegral pHdrSz
      , fromIntegral hashLen , fromIntegral symTabSz , relSz , fromIntegral dynTabSz
      , fromIntegral interpsz , fromIntegral strtabSz]

  dynTab  = (\(ty , val) -> Elf64_Dyn (fromIntegral (fromEnum ty)) (fromIntegral val)) <$>
    [ (DT_STRTAB , strTabOff) , (DT_STRSZ ,  strtabSz)
    , (DT_SYMTAB , symTabOff) , (DT_SYMENT ,  elf64_SymSz)
    , (DT_REL    , relOff) , (DT_RELSZ  , relSz * V.length relTab) , (DT_RELENT ,  relSz)
    , (DT_HASH   , hashOff)
    , (DT_NEEDED , strTabOff + 1 {-skip null start byte-})-- libcName) -- ! find offset of libc
    , (DT_NULL , 0)] -- must have empty last entry

  eHdr = elf64x86Template
    { e_phoff = fromIntegral elfHdrSz -- setup prog headers right after ehdr
    , e_phnum = 3
    , e_entry = fromIntegral textOff
    , e_type = fromIntegral (fromEnum ET_EXEC)
    }
  ptrWord = fromIntegral (ptrToIntPtr ptr)
  pInterp = mkPHdr PT_INTERP pfR interpsz (fromIntegral interpOff)
  pDyn    = mkPHdr PT_DYNAMIC (pfR .|. pfW) (fromIntegral dynTabSz) (fromIntegral dynOff)
  in do
  poke (plusPtr ptr eHdrOff) eHdr
  poke (plusPtr ptr pInterpOff) pInterp
  -- -> insert pLoad here, once we know filesz | memsz | progSz
  poke (plusPtr ptr pDynOff) pDyn
  traceShowM hashInfo
  writeHashTab (plusPtr ptr (fromIntegral hashOff  )) hashInfo
--foldM push (plusPtr ptr (fromIntegral hashOff  )) ([0,0,0,0,0] :: [Word32])
  writeSymTab  (plusPtr ptr (fromIntegral symTabOff)) symbols
  V.foldM push (plusPtr ptr (fromIntegral relOff   )) relTab
  writeDynTab  (plusPtr ptr (fromIntegral dynOff   )) dynTab
  -- v interp need not be null terminated as strTab immediately follows and must start with '\0' anyway
  BSU.unsafeUseAsCString interp $ \cstr ->
    copyBytes (plusPtr ptr (fromIntegral interpOff)) (castPtr cstr) (B.length interp)
  writeStrTab  (plusPtr ptr (fromIntegral strTabOff)) extSymbols
  progSz <- fromIntegral <$>
    X86.mkAsm memSz (plusPtr ptr (fromIntegral textOff)) progText
  let filesz = progSz + fromIntegral textOff
  -- v rewrite the pLoad program header now we know file size
      pLoad  = mkPHdr PT_LOAD (pfR .|. pfW .|. pfX) (fromIntegral progSz) 0 -- { pOffset = fromIntegral textOff }
  pokeByteOff ptr (fromIntegral pLoadOff) pLoad { pmemsz = filesz , pfilesz = filesz }
  pure (fromIntegral filesz)

test = do
  let jitsz = 0x40000
      syms = V.fromList ["libc.so.6" , "puts"]
      nHashBuckets = fromIntegral (V.length syms - 1)
      interpreter = "/nix/store/dg8mpqqykmw9c7l0bgzzb5znkymlbfjw-glibc-2.37-8/lib/ld-linux-x86-64.so.2"
  ptr <- mmap nullPtr jitsz (protRead .|. protWrite) (mmapAnon .|. mmapPrivate) (-1) 0
  filesz <- mkDynElf (castPtr ptr) (fromIntegral jitsz) nHashBuckets interpreter 1 syms mempty X86.testVecs

  bs <- BSU.unsafePackCStringLen (castPtr ptr , filesz)

  -- TODO use openTempfile or perhaps delete this simply
  B.writeFile "/tmp/asm.out" bs
  readProcess "readelf" ["-all", "-s" , "/tmp/asm.out"] "" >>= putStrLn
  readProcess "objdump" ["--all" , "-d", "-Mintel" , "-mi386:x86-64" , "/tmp/asm.out"] "" >>= putStrLn
  -- add -R flag to odjdump for relocation entries
  -- Version References ? VERNEEDED VERSYM

testElf :: IO Elf
testElf = do
--handle <- openFile "./irie" ReadMode
  mmapWithFilePtr "/run/current-system/sw/bin/ls" ReadOnly Nothing $ \(fp , sz) -> do
    elf <- peek (castPtr fp) :: IO Elf
    pure elf
