{-# Language TemplateHaskell #-}
module CoreToX86 where
import X86
import Externs
import CoreSyn
import Prim
import Data.Functor.Foldable
import qualified Data.Vector as V
import Control.Lens
import Foreign.Ptr

data CPUState = CPUState
 { _regs         :: V.Vector (Maybe Word64 , Int) -- register state (track constants)
-- , _flagCarry    :: Bool
-- , _flagOverflow :: Bool
 , _spills       :: [Reg]
 }; makeLenses ''CPUState
startCPUState = CPUState mempty []

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

type SizeT = Int -- Word64 probably more useful on 64-bit pointer size system
data Value
  = Reg Reg AsmType -- can index all registers incl xmm etc, based on asmtype
  | Prod (V.Vector Reg) AsmType
  deriving Show

data AsmType
 = Bits Int -- most normal is 64 , can extend to any size but may spill. (16 ymm regs = 4096 bits)
 | ProdTy Int (V.Vector Int)
-- | PackedBits Int (V.Vector Int) -- pack into registers using bitshifts
 | Mem SizeT
 deriving Show

data AsmState = AsmState
 { _cpuState     :: CPUState
 , _retLoc       :: Value
 , _memLen       :: Int
 , _memPtr       :: Ptr Word8
 }; makeLenses ''AsmState

writeAsm :: [Immediate] -> AsmM ()
writeAsm prog = use memPtr >>= \ptr -> use memLen >>= \len -> liftIO (X86.mkAsm len ptr prog) >>=
  \wroteLen -> memPtr %= \p -> plusPtr p wroteLen

type AsmM = StateT AsmState IO
mkAsmF :: ModuleIName -> V.Vector LoadedMod -> V.Vector Word32
  -> TermF (AsmM Value) -> AsmM Value
mkAsmF thisM loadedMods localBinds = let
  f = Reg RAX (Bits 64) <$ writeAsm hlt -- a TODO placeholder
  -- find best register(s) for subexpression e : ty
  getReg :: PrimType -> AsmM Value
  getReg ty = pure (Reg RAX (Bits 64))
  in \case
  VBruijnF i -> f
  VarF (VQBindIndex q) -> f
  LitF (Fin 32 i) -> getReg (PrimInt 32) >>= \val -> val <$ case val of
    Reg r _ -> writeAsm (movImm32 r (fromIntegral i))
  InstrF i -> f
  CastF c t -> f

  -- Figure out calling convention based on type of f: rip-relative
  AppF f ars -> sequence ars >>= \args -> _

  ArrayF ars -> f
  TupleF ars -> f
  TTLensF scrut [field] lensOP -> f

  LabelF l ars -> f -- do what tuple does, mk label when subcasted into sumtype
  CaseBF scrut _t alts def -> f

  x -> error $ show (embed (Question <$ x))

bindToAsm :: ModuleIName -> V.Vector LoadedMod -> V.Vector Word32 -> (Ptr Word8 , Int) -> Expr -> IO (Ptr Word8)
bindToAsm thisM loadedMods localBinds (memPtr' , memLen') (Core term ty) = let
  cgBind = cata (mkAsmF thisM loadedMods localBinds) term *> writeAsm ret
  in do
  (_retValue , asmState) <- cgBind `runStateT` AsmState
    { _cpuState = startCPUState
    , _retLoc   = Reg RAX (Bits 64) -- TODO conv ty!
    , _memLen   = memLen'
    , _memPtr   = memPtr'
    }
  pure (asmState ^. memPtr)

-- TODO also return sym+strtable of labels & local function names
-- syms = offset & strName
mkAsmBindings :: ModuleIName -> V.Vector LoadedMod -> V.Vector (LetMeta , Bind) -> (Ptr Word8 , Int)
  -> IO (Ptr Word8 , (Maybe Word64 , [(Word64 , ByteString)])) -- return endPtr and entrypoint relative to start of .txt section
mkAsmBindings modIName loadedMods lets (memPtr , memLen) = let
  bindOffs = mempty -- offsets to previously defined bindings (also needed for emitting symbols)
  -- sequentially write out all functions & collect their offsets for strtable purposes
  go (ptr , offs) (lm , bind) = let
    nm = (letBindIndex lm) & \(VQBindIndex q) -> lookupBindName loadedMods (modName q) (unQName q)
    in case bind of
    BindOK opt rhs -> bindToAsm modIName loadedMods bindOffs (ptr , memLen) rhs -- TODO memlen
      <&> \endPtr -> (endPtr , maybe offs (\nm -> (fromIntegral (minusPtr ptr memPtr) , encodeUtf8 nm) : offs) nm)
  in do
  entryEndPtr <- X86.mkAsm' memLen memPtr (concat X86.exitSysCall) -- (concat X86.writeSysCall)
  let entrySym = [(0 , "_e_entry")]
  (endPtr , syms) <- foldM go (entryEndPtr , entrySym) lets
  traceShowM syms

  pure (endPtr , (Just (fromIntegral $ minusPtr endPtr memPtr) , syms)) -- main entry is our exit syscall
