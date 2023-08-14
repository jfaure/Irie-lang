{-# LANGUAGE DeriveGeneric, DeriveAnyClass , TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin=Foreign.Storable.Generic.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt=Foreign.Storable.Generic.Plugin:-v1 #-}
module Elf where
import Data.Bits
import Foreign.Storable.Generic
import qualified Data.ByteString as B
import qualified Data.ByteString.Unsafe as BSU
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector.Algorithms.Heap as VU
import Foreign.Ptr
import Foreign.Marshal.Utils
import CMMap
import System.Process
import qualified X86
import Control.Lens

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
  , pOffset :: ElfN_Off -- offset from file beginning to segment
  , pvaddr  :: ElfN_Addr
  , ppaddr  :: ElfN_Addr -- irrelevant on virtual memory, BSD requries 0
  , pfilesz :: Word64 -- number of bytes of segment, can be 0
  , pmemsz  :: Word64 -- number of bytes in memory of segment, can be 0
  , palign  :: Word64 -- 0|1 means no alignement required, else must be +power 2
  } deriving (Show, Read, Generic, GStorable)
data PType = PT_NULL | PT_LOAD | PT_DYNAMIC | PT_INTERP | PT_NOTE | PT_SHLIB | PT_PHDR | PT_TLS deriving Enum
(pfR , pfW , pfX) = (4 , 2 , 1) :: (Word32 , Word32 , Word32)
emptyPHdr = Phdr 0 0 0 0 0 0 0 0
pHdrSz = sizeOf emptyPHdr

data Elf64_Shdr = Elf64_Shdr
  { sName      :: Word32  -- ^ Section name
  , sType      :: Word32  -- ^ Section type
  , sFlags     :: WordXX  -- ^ Section attributes
  , sAddr      :: WordXX  -- ^ Virtual address in memory
  , sOffset    :: WordXX  -- ^ Offset in file
  , sSize      :: WordXX  -- ^ Size of section
  , sLink      :: Word32  -- ^ Link to other section
  , sInfo      :: Word32  -- ^ Miscellaneous information (eg. size of symtable iff SHT_SYMTAB)
  , sAddrAlign :: WordXX  -- ^ Address alignment boundary
  , sEntSize   :: WordXX  -- ^ Size of entries, if section has table
  } deriving (Show, Read, Generic, GStorable)
data SHT = SHT_NULL | SHT_PROGBITS | SHT_SYMTAB | SHT_STRTAB | SHT_RELA | SHT_HASH | SHT_DYNAMIC | SHT_NOTE | SHT_NOBITS | SHT_REL | SHT_SHLIB | SHT_DYNSYM deriving Enum
(shfWrite , shfAlloc , shfExec) = (1 , 2 , 4) :: (Word64 , Word64 , Word64)
emptySHdr = Elf64_Shdr 0 0 0 0 0 0 0 0 0 0 :: Elf64_Shdr
sHdrSz = sizeOf emptySHdr

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
--   else deref chains: chain[ix] is index of next symbol (0 = STN_UNDEF = end of chain)
-- eg. 1 2 1 0 0 = 1 bucket , 2 syms , bucket1 starts with symbol 1 , null symbol , end of single chain
-- Since chain indexes are symbol table names, we need as many chains as symbols
-- Chain vector (symbol indexes) is a groupBy on hash%nBuckets , ending in 0
mkHash :: Word32 -> VU.Vector Word32 -> (HashHeader , V.Vector Word32 , V.Vector Word32)
mkHash nBuckets syms' = let syms = VU.cons 0 syms' ; nChains = VU.length syms
  in runST $ do -- first symbol must be STN_UNDEF
  hashes <- VU.unsafeThaw (VU.indexed $ VU.map (\s -> mod s nBuckets) syms)
  VU.sortBy (on compare snd) hashes -- group symbol names that hash >> mod to same value
  hashV <- VU.unsafeFreeze hashes
  -- ^ : VU.Vector (Int , Word32) -- eg: [ (5 , h0 , 2 , h0 , 6 , h1 , 1 , h1) ]
  chains  <- MV.new nChains
  buckets <- MV.replicate (fromIntegral nBuckets) 0
  -- v walk the groupBy , each time hash/nBuckets changes, end chain & init bucket.
  -- ! indexes start at 1
  -- This looks at elems 2 at a time: the current vals and the next
  VU.head hashV & \(sym0 , h0) -> MV.write buckets (fromIntegral h0) (fromIntegral sym0)
  let go (prevSymIdx , prevHashMod) next@(symIdx , hashMod) = next <$ do
        if prevHashMod == hashMod
        then MV.write chains prevSymIdx (fromIntegral symIdx)
        else MV.write chains prevSymIdx 0 *> MV.write buckets (fromIntegral hashMod) (fromIntegral symIdx)
  VU.fold1M go hashV >>= \(lastSym , _lastHash) -> MV.write chains lastSym 0

  (HashHeader nBuckets (fromIntegral nChains) ,,)
    <$> V.unsafeFreeze buckets <*> V.unsafeFreeze chains

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
  go :: Ptr Elf64_Dyn -> Elf64_Dyn -> IO (Ptr Elf64_Dyn)
  go ptr dyn = plusPtr ptr (sizeOf emptyDyn) <$ poke ptr dyn
  in castPtr <$> V.foldM go (castPtr mem) (V.fromList dyns)

writeStrTab :: Ptr Word8 -> V.Vector ByteString -> IO (Ptr Word8)
writeStrTab ptr strs = let
  go acc bs = let blen = B.length bs in do
    BSU.unsafeUseAsCString bs $ \cstr -> copyBytes acc (castPtr cstr) blen
    plusPtr acc (blen + 1) <$ pokeByteOff acc blen (0 :: Word8)
  in poke ptr (0 :: Word8) *> V.foldM go (plusPtr ptr 1) strs

writeHashTab :: Ptr Word8 -> (HashHeader , V.Vector Word32 , V.Vector Word32) -> IO (Ptr Word8)
writeHashTab mem' (hashHdr , hashBuckets , hashChains) = let mem = castPtr mem' in do
  bucketPtr <- plusPtr mem hashHdrSz <$ poke mem hashHdr
  chainPtr  <- V.foldM pushDWord bucketPtr hashBuckets
  castPtr <$> V.foldM pushDWord (castPtr chainPtr) hashChains

-- v Must start with zeroed symbol
-- strNames are offsets into the symbol table
writeSymTab :: Ptr Word8 -> V.Vector Elf64_Sym -> IO (Ptr Word8)
writeSymTab mem symVec = poke (castPtr mem) emptyElf64_Sym *> -- empty sym
  V.foldM (\ptr sym -> plusPtr ptr elf64_SymSz <$ poke (castPtr ptr) sym) (plusPtr mem elf64_SymSz) symVec

-- Elf | List ProgHeaders | hashTable | SymTable | Relocations | DynTab | InterpStr | StrTab | Text | Shdrs
-- ! Must know in advance: nProgHeaders , nSyms , nBuckets , sizeOf str
-- The rest can be appended and their locations patched into the prog headers
-- * Idea is to place ehdr , progheaders , append everything 1 by 1 , then SHdrs
data ElfM = ElfM
  { _elfptr    :: Ptr Word8
  , _ptrSz     :: Int
  , _pHdrsSet  :: (Int , BitSet) -- runtime Sanity checking that all phdrs are written exactly once
  , _elfEndPtr :: Ptr Word8
  , _elfShdrs  :: ![(Elf64_Shdr , ByteString)]
  }; makeLenses ''ElfM

-- elf start requires nProgHeaders + all dynamic info(hash,sym/reloc/dyntab) up front
startElf ptr memSz nProgH = ElfM
  { _elfptr    = ptr
  , _ptrSz     = memSz
  , _pHdrsSet  = (nProgH , 0)
  , _elfEndPtr = plusPtr ptr (elfHdrSz + nProgH * pHdrSz)
  , _elfShdrs  = []
  }

addSection  :: ElfM -> Maybe (Int , Phdr) -> Elf64_Shdr -> ((Ptr Word8 , Int) -> IO (Ptr Word8 , a))
  -> IO (ElfM , a)
addSection elf phdr shdr writeSegment = do
  let segmentStart = elf ^. elfEndPtr
  (segmentEnd , clientData) <- writeSegment (segmentStart , elf ^. ptrSz)
  let segOff = fromIntegral $ minusPtr segmentStart (elf ^. elfptr)
      segSz  = fromIntegral (minusPtr segmentEnd segmentStart)

  case phdr of
    Nothing -> pure ()
    Just (i , p) -> poke (plusPtr (elf ^. elfptr) (elfHdrSz + i * pHdrSz)) p
      { pOffset = 0 -- segOff segfaults, apparently need to load full segment.. TODO
      , pfilesz = segSz + segOff , pmemsz = segSz + segOff
--    , pvaddr  = {-filePtr +-} segOff , ppaddr = segOff -- filePtr + off
      }
  pure ( elf & elfShdrs %~ ((shdr { sOffset = segOff , sSize = segSz} , ".shname") :) & elfEndPtr .~ segmentEnd
       , clientData )

-- Write section headers and elf header
finaliseElf :: ElfM -> Word16 -> ElfN_Addr -> IO Int -- Append all section headers, set e_entry, check pHdrs all set
finaliseElf elf shstrndx entry = do
  let shPtr = elf ^. elfEndPtr
      shNum = 1 + length (elf ^. elfShdrs)
  poke (castPtr shPtr) emptySHdr
  foldM (\indx shdr -> (indx - 1) <$ pokeByteOff shPtr (sHdrSz * indx) shdr) (shNum - 1) (fst <$> (elf ^. elfShdrs))
  let shOff  = minusPtr shPtr (elf ^. elfptr) 
      fileSz = shOff + shNum * sHdrSz

  poke (castPtr (elf ^. elfptr)) elf64x86Template
    { e_phoff = fromIntegral elfHdrSz -- setup prog headers right after ehdr
    , e_phnum = fromIntegral $ fst (elf ^. pHdrsSet)
    , e_type  = fromIntegral (fromEnum ET_DYN) -- ET_EXEC)
    , e_shnum = fromIntegral shNum
    , e_shoff = fromIntegral shOff
    , e_shstrndx = shstrndx -- fromIntegral strTabIx -- TODO write strtabs and their names!
    , e_entry = entry
    }
  pure fileSz

-- nHashBuckets should be >0 , <= length extSymbols
-- RelTab contains all addresses where a relocation needs to be inserted , + index into sym table
-- ! DynSection DT_NEEDED library names are strtab offsets (DT_STRTab key)
-- TODO: ld-linux segfaults on low indices of our strTable
mkDynElf :: Ptr Word8 -> Int -> Word32 -> ByteString -> Int -> Int -> V.Vector ByteString -> V.Vector Elf64_Rel
  -> _ -> IO Int
mkDynElf ptr memSz nHashBuckets interp libcName runpathName extSymbols relTab writeProg = let
  -- calc sizes , then can write directly to mem
  strTabOffs = V.scanl (\acc bs -> acc + B.length bs + 1) 1 extSymbols -- account for null bytes (incl start null)
  strtabSz = V.last strTabOffs
  nExterns = V.length extSymbols
  symbols = let -- symbol stNames index the strtab
    mkSym i = emptyElf64_Sym { stName = fromIntegral (strTabOffs V.! i) , stInfo = mkSTInfo STB_GLOBAL STT_FUNC }
    in V.generate nExterns mkSym 
  symTabSz = (1 + nExterns) * elf64_SymSz -- This must be precalculated correctly !

  hashedSyms = VU.generate (V.length extSymbols) $ \i -> elfHash (extSymbols V.! i)
    -- & \h -> d_ (extSymbols V.! i , h , mod h nHashBuckets) h
  hashInfo@(hashHdr , hashBuckets , hashChains) = mkHash nHashBuckets hashedSyms
  hashLen = hashHdrSz + 4 * (length hashBuckets + V.length hashChains) -- same as symbol count
  interpsz = fromIntegral (B.length interp) -- can skip null byte since we place strtab right after this

  -- ! set this in advance of knowing dynTab
  dynTabSz = length dynTab{-9-} * sizeOf (Elf64_Dyn 0 0)

  -- This is the order we layout the headers contiguously, thus offsets are a scanl
  [eHdrOff , pInterpOff , pLoadOff , pDynOff , hashOff , symTabOff , relOff , dynOff , interpOff , strTabOff , textOff ]
    = scanl (+) 0 [fromIntegral elfHdrSz , fromIntegral pHdrSz , fromIntegral pHdrSz , fromIntegral pHdrSz
      , fromIntegral hashLen , fromIntegral symTabSz , relSz , fromIntegral dynTabSz
      , fromIntegral interpsz, fromIntegral strtabSz]

  dynTab  = (\(ty , val) -> Elf64_Dyn (fromIntegral (fromEnum ty)) (fromIntegral val)) <$>
    [ (DT_NEEDED , libcName) -- ! find offset of libc
    , (DT_RPATH  , runpathName) -- rpath is deprecated in favor of runpath so ld_preload can override
    , (DT_HASH   , hashOff)
    , (DT_STRTAB , strTabOff) , (DT_STRSZ , strtabSz)
    , (DT_SYMTAB , symTabOff) , (DT_SYMENT , elf64_SymSz)
    , (DT_REL    , relOff) , (DT_RELSZ  , relSz * V.length relTab) , (DT_RELENT ,  relSz)
    , (DT_NULL , 0)] -- must have empty last entry

  eHdr = elf64x86Template
    { e_phoff = fromIntegral elfHdrSz -- setup prog headers right after ehdr
    , e_phnum = 3
    , e_type = fromIntegral (fromEnum ET_DYN) -- ET_EXEC)
    }

  pInterp = mkPHdr PT_NULL pfR interpsz (fromIntegral interpOff) -- TODO temp HACK no interpreter
--pInterp = mkPHdr PT_INTERP pfR interpsz (fromIntegral interpOff)
  pDyn    = mkPHdr PT_DYNAMIC (pfR .|. pfW) (fromIntegral dynTabSz) (fromIntegral dynOff)
  in do
  -- -> insert eHdr , once sections known
  poke (plusPtr ptr pInterpOff) pInterp
  -- -> insert pLoad here, once we know filesz | memsz | progSz
  poke (plusPtr ptr pDynOff) pDyn
  wroteHash <- writeHashTab (plusPtr ptr (fromIntegral hashOff  )) hashInfo
  when (minusPtr wroteHash (plusPtr ptr (fromIntegral hashOff)) /= hashLen) (error "Miscalculated symtabsz")
  wroteSymTab <- writeSymTab  (plusPtr ptr (fromIntegral symTabOff)) symbols
  when (minusPtr wroteSymTab (plusPtr ptr (fromIntegral symTabOff)) /= symTabSz) (error "Miscalculated symtabsz")
  V.foldM push (plusPtr ptr (fromIntegral relOff   )) relTab
  writeDynTab  (plusPtr ptr (fromIntegral dynOff   )) dynTab
  BSU.unsafeUseAsCString interp $ \cstr -> -- skip '\0' since strtab must start with one
    copyBytes (plusPtr ptr (fromIntegral interpOff)) (castPtr cstr) (B.length interp)
  strTabWrittenLen <- writeStrTab  (plusPtr ptr (fromIntegral strTabOff)) extSymbols
  when (minusPtr strTabWrittenLen (plusPtr ptr (fromIntegral strTabOff)) /= strtabSz) (error "Miscalculated strtablen")

  (progEnd , progEntry , syms) <- writeProg (plusPtr ptr (fromIntegral textOff) , memSz)
    :: IO (Ptr Word8 , Maybe Word64 , [(Word64 , ByteString)])
  let progSz = fromIntegral $ minusPtr progEnd (plusPtr ptr (fromIntegral textOff))
      loadSz = progSz + fromIntegral textOff
  -- v rewrite the pLoad program header now we know file size

  -- write headers now sizes are known
  pokeByteOff ptr (fromIntegral pLoadOff) $
    (mkPHdr PT_LOAD (pfR .|. pfW .|. pfX) (fromIntegral loadSz) 0) { pmemsz = loadSz , pfilesz = loadSz }

  -- Must start with null Shdr
  let shNum = 4
      strTabIx = 1
--    nullShdr = emptySHdr
      strTabShdr = emptySHdr { sName = 0 , sType = fromIntegral (fromEnum SHT_STRTAB)
        , sFlags = shfAlloc , sOffset = fromIntegral strTabOff , sSize = fromIntegral strtabSz }
      textShdr off sz = emptySHdr { sName = 0 , sType = fromIntegral (fromEnum SHT_PROGBITS)
        , sFlags = shfAlloc .|. shfExec , sOffset = off , sSize = sz }
      symTabShdr = emptySHdr { sName = 0 , sType = fromIntegral (fromEnum SHT_SYMTAB)
        , sOffset = fromIntegral symTabOff , sSize = fromIntegral symTabSz
        , sEntSize = fromIntegral elf64_SymSz , sLink = strTabIx}
  poke (castPtr progEnd) emptySHdr
  poke (castPtr (plusPtr progEnd (1 * sHdrSz))) strTabShdr
  poke (castPtr (plusPtr progEnd (2 * sHdrSz))) (textShdr (fromIntegral textOff) progSz)
  poke (castPtr (plusPtr progEnd (3 * sHdrSz))) symTabShdr

  poke (plusPtr ptr eHdrOff) eHdr
    { e_shnum = shNum
    , e_shoff = fromIntegral (minusPtr progEnd ptr)
    , e_shstrndx = fromIntegral strTabIx
    , e_entry = maybe 0 (+ fromIntegral textOff) progEntry
    }
  pure (fromIntegral loadSz + fromIntegral shNum * sHdrSz)

test prog = do
  let jitsz = 0x40000
      libcStr = "libc.so.6"
      syms = V.fromList [libcStr , rPath  , "puts" , "exit" , "printf"]
      rPath = "/nix/store/6n802p0lms8pfp11alna7jl4icjvwhzv-shell/lib64:/nix/store/6n802p0lms8pfp11alna7jl4icjvwhzv-shell/lib:/nix/store/fz33c1mfi2krpg1lwzizfw28kj705yg0-glibc-2.34-210/lib:/nix/store/8dn12i3d7harw8g7dzk6dy7c5diz5ibp-gcc-11.3.0-lib/lib"
      libcName = 1 -- offsets into flattened strtable , starts after null byte!
      rPathName = 1 + B.length libcStr + 1
      nHashBuckets = fromIntegral (V.length syms - 1)
      interpreter = "/nix/store/fz33c1mfi2krpg1lwzizfw28kj705yg0-glibc-2.34-210/lib/ld-linux-x86-64.so.2"
  ptr <- mmap nullPtr jitsz (protRead .|. protWrite) (mmapAnon .|. mmapPrivate) (-1) 0
  filesz <- mkDynElf (castPtr ptr) (fromIntegral jitsz) nHashBuckets interpreter libcName rPathName syms mempty
    (\(ptr , memSz) -> X86.mkAsm' memSz ptr (concat prog) <&> (,Just 0 , mempty))

  bs <- BSU.unsafePackCStringLen (castPtr ptr , filesz)

  -- TODO use openTempfile or perhaps delete this simply
  B.writeFile "/tmp/asm.out" bs
  void $ readProcess "chmod" ["+x", "/tmp/asm.out"] ""
  readProcess "readelf" ["-all", "-s" , "/tmp/asm.out"] "" >>= putStrLn
  readProcess "objdump" ["--all" , "-d", "-Mintel" , "-mi386:x86-64" , "/tmp/asm.out"] "" >>= putStrLn
  -- add -R flag to odjdump for relocation entries
  -- Version References ? VERNEEDED VERSYM

-- ! Programs must call exit syscall at some point
mkElf :: (Bool , Bool) -> ((Ptr Word8 , Int) -> IO (Ptr Word8 , (Word64 , [(Word64 , ByteString)]))) -> IO ()
mkElf (disassElf , runElf) mkProg = let
--mkProg (ptr , memSz) = X86.mkAsm memSz ptr (concat X86.writeSysCall) <&> \sz -> (plusPtr ptr sz , Just 0)
  jitsz = 0x40000
--rPathName = 1 ; libcName  = 1 ; syms = mempty ; interpreter = "" ; nHashBuckets = 1
  outFile = "/tmp/runAsm.out" 
  in do
  ptr <- mmap nullPtr jitsz (protRead .|. protWrite) (mmapAnon .|. mmapPrivate) (-1) 0
--filesz <- mkDynElf (castPtr ptr) (fromIntegral jitsz) nHashBuckets interpreter libcName rPathName syms mempty mkProg
-- vv TODO don't hardcode sName and section strtab offsets
  let elfM = startElf ptr (fromIntegral jitsz) 1{-nProgHdrs-}
      txtPhdr = emptyPHdr { pType = fromIntegral (fromEnum PT_LOAD) , pFlags = (pfR .|. pfW .|. pfX)}
      txtShdr = emptySHdr { sName = 1 , sType = fromIntegral (fromEnum SHT_PROGBITS) , sFlags = shfAlloc .|. shfExec }
      shstrTabShdr = emptySHdr { sName = 7 , sType = fromIntegral (fromEnum SHT_STRTAB) , sFlags = shfAlloc }
      txtOff = minusPtr (elfM ^. elfEndPtr) (elfM ^. elfptr)
      shstrs = V.fromList [".text" , ".shstrtab" , ".strtab" , ".symtab"] -- TODO let finaliseElf handle this one
  (elfM1 , (phent , syms)) <- addSection elfM (Just (0{-phdrIdx-} , txtPhdr)) txtShdr (\inp -> mkProg inp)
  (elfM2 , ()) <- addSection elfM1 Nothing shstrTabShdr (\(inp,_) -> (,()) <$> writeStrTab inp shstrs)
  let symStrs = V.fromList (snd <$> syms)
  (elfM3 , ()) <- let
    symStrShdr = emptySHdr { sName = 17 , sType = fromIntegral (fromEnum SHT_STRTAB) }
    in addSection elfM2 Nothing symStrShdr (\(inp,_) -> (,()) <$> writeStrTab inp symStrs)
  (elfM4 , ()) <- let
    symOffs = V.scanl (\acc bs -> acc + B.length bs + 1) 1 symStrs
    elfSyms = (flip Prelude.imap) syms $ \i (off , _) -> emptyElf64_Sym
      { stName = fromIntegral (symOffs V.! i) {-strtaboffs!-}
      , stValue = fromIntegral off
      , stInfo = mkSTInfo STB_GLOBAL STT_FUNC
      , stShNdx = 1 } -- ! txt section idx
    symTabShdr = emptySHdr { sName = 25 , sType = fromIntegral (fromEnum SHT_SYMTAB)
      , sEntSize = fromIntegral elf64_SymSz
      , sInfo = fromIntegral (V.length symStrs)
      , sLink = 3 } -- ! the strtable for these syms
    in addSection elfM3 Nothing symTabShdr (\(inp,_) -> (,()) <$> writeSymTab inp (V.fromList elfSyms))
  filesz <- finaliseElf elfM4 2{-shstrndx-} (fromIntegral txtOff + phent)

  bs <- BSU.unsafePackCStringLen (castPtr ptr , filesz)
  B.writeFile outFile bs
  void $ readProcess "chmod" ["+x", outFile] ""
--readProcess "readelf" ["-all", "-s" , outFile] "" >>= putStrLn
  when disassElf $ readProcess "objdump" ["-d" , "-Mintel" , "--visualize-jumps=color" , "--disassembler-color=on", outFile] "" >>= putStrLn
--visualize-jumps[=color
  when runElf $ do
    putStrLn @Text "Running elf..."
    (exitCode , asmStdout , asmStderr) <- readProcessWithExitCode outFile [] ""
    putStrLn asmStdout
    print exitCode

test1 = test X86.writeSysCall -- exitSysCall
