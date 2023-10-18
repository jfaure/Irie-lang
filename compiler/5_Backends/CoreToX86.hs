{-# Language TemplateHaskell #-}
module CoreToX86 where
import qualified X86
import Externs
import CoreSyn
import Prim
import Data.Functor.Foldable
import Data.Functor.Foldable.TH
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector.Unboxed.Mutable as MVU
import qualified BitSetMap as BSM
import qualified Foreign.Storable
import qualified Data.IntMap as IM
import Control.Lens
import Foreign.Ptr
import PrettyCore
import Control.Monad.Trans.Cont

-- TODO. multiply by constant use lea: esp. 3 5 9

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
  | VJmpCond X86.JmpCond -- Use set[le..] to get flag into a register
  | StackSlot Int AsmType -- relative to fn base pointer
  deriving (Show , Eq)

-- 1. Args  -> ADTs (of Atoms)
-- 2. Atoms -> RegMem
-- * Some atoms can be force assigned to physical registers (calling conv)
-- * ana can figure out [Atom]->[Atom] of RPN & organise fn call preservation
--type RegMem = Either X86.Reg Int -- offset from initial RSP
--type Atom = Int
--type Atoms = MV.IOVector (Maybe RegMem)

data RPNInstr = UnOp PrimInstr | BinOp PrimInstr | ImmOp PrimInstr Literal deriving Show
data RetNode
  = SetLit    Literal
  | ArgReg    Int
  | CallQName Bool QName [RetNode] -- isTailCall

  -- 1. running RPN may free registers.
  -- 2. Use RAX as much as possible. (shorter instrs)
  -- 3. Must respect calling conventions when computing the stack
  -- 4. Must End in retloc (unless ifElse cond)
  -- inp stack (forced calling convs) & rpn instructions (dependency chain)
  | RPN [RetNode] [RPNInstr]

  | IfElse Bool RetNode RetNode RetNode
  | Ret Value RetNode
  deriving Show; makeBaseFunctor ''RetNode
instance Show (RetNodeF ())

-- a foldl on semi-flattened term tree (only flatten AppInstr nodes)
-- Point is to clarify separation of calling-convention nodes and nodes that don't care
-- Also the tree is now in asm order, with nodes executed first: In fact the '++' indicates overlappable instrs
-- ! regs always end up in lOp
mkRPN :: ([Term] , [RPNInstr]) -> [Term] -> ([Term] , [RPNInstr])
mkRPN acc [] = acc
mkRPN (as , ai) (term : argsR) = case term of
  -- vv TODO mark overlappable instruction start (instead of ++)
  App (Instr i) argsL -> case argsL of -- TODO Only iff i commutative!
    [l , Lit lit]                   -> mkRPN (as , ImmOp i lit : ai) (argsR ++ [l])
    [Lit lit , r] | isCommutative i -> mkRPN (as , ImmOp i lit : ai) (argsR ++ [r])
    argsL | arity i == 2 -> mkRPN (as , BinOp i : ai) (argsR ++ argsL)
    argsL | arity i == 1 -> mkRPN (as , UnOp i : ai) (argsR ++ argsL)
  x -> mkRPN (x : as , ai) argsR

-- Conv. to RPN , mark TOP for ret
-- TODO: which reg to destroy in 2-op instr?
type RegMachineState = ()
mkRegMachineU :: _ -> _ -> Bool -> (RegMachineState , Term)
  -> RetNodeF (RegMachineState , Term)
mkRegMachineU argVals retVal isTop (st , term) = case term of
  Top t -> case t of -- We care about tail calls and ret-ting out of branches
    CaseB{}     -> mkRegMachineU argVals retVal True (st , t)
    App Var{} _ -> mkRegMachineU argVals retVal True (st , t)
    t       -> RetF retVal (st , t)
  Lit l       -> SetLitF l
  VBruijn i   -> ArgRegF i

--App (Instr i) args -> mkRPN ([] , [Left i]) args & \(as , ai) -> RPNF ((st,) <$> as) ai
  App (Instr i) args -> mkRPN ([] , []) [term] & \(as , ai) -> RPNF ((st,) <$> as) ai
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

  , _stackSz  :: Int -- track number of push instructions
  , _liveRegs :: Word16 -- bitset
  , _regDups  :: VU.Vector Int -- read from calling convention + bruijnAbs
  , _argRegs  :: V.Vector Value
  }; makeLenses ''MkX86State
type MkX86M = StateT MkX86State IO
writeAsm :: [X86.Immediate] -> MkX86M ()
writeAsm prog = use memPtr >>= \ptr -> use memLen >>= \len ->
  liftIO (X86.mkAsm len ptr prog) >>= \wroteLen -> memPtr %= (`plusPtr` wroteLen)
writeAsmAt ptr prog = liftIO (X86.mkAsm 15 {-max len for an instruction-} ptr prog)

-- Reset reg/stack/flags state for each branch of case statement
svState :: MkX86M (Word16 , VU.Vector Int , V.Vector Value)
svState = (\l r a -> (l,r,a)) <$> use liveRegs <*> use regDups <*> use argRegs
restoreState :: (Word16 , VU.Vector Int , V.Vector Value) -> MkX86M ()
restoreState (live , rd , ar) = void $ (liveRegs .= live) *> (regDups .= rd) *> (argRegs .= ar)

-- reg will be overwritten, so sv it somewhere else and re-point the arg env
reassign :: X86.Reg -> Maybe X86.Reg -> MkX86M ()
reassign r y = use argRegs >>= \ab -> let
  rI = fromEnum r
  Just i = V.findIndex (\(Reg reg _) -> r == reg) ab
  in do
  regDups %= \rDups -> amendU rDups rI 0
  case y of 
    Just ry -> argRegs .= amend ab i (Reg ry (Bits 32)) -- TODO hack type
    Nothing -> (stackSz <<+= 8) >>= \slot -> do
      writeAsm (X86.push r)
      argRegs .= amend ab i (StackSlot slot (Bits 64))

-- destructive operations want to overwrite one of their regs
-- Also mark a use of this reg
inPlaceReg :: X86.Reg -> MkX86M Bool
inPlaceReg r = use regDups >>= \rDups -> let
  rI = fromEnum r
  n  = rDups VU.! rI
  ok = n <= 1
  in ok <$ when (n > 0) (regDups %= \r -> amendU r rI (n - 1)) -- record a use

-- ensure a reg is marked in-use (eg. ret regs after returning from a fn call)
setRegInUse :: X86.Reg -> MkX86M ()
setRegInUse r = liveRegs %= (`clearBit` fromEnum r)

freeReg :: X86.Reg -> MkX86M Bool
freeReg r = use regDups >>= \rDups -> let
  rI = fromEnum r
  rN = rDups VU.! rI
  canFree = rN <= 1
  in canFree <$ if canFree
  then liveRegs %= (`setBit` fromEnum r)
  else regDups .= (amendU rDups rI (rN - 1))

allocReg :: MkX86M X86.Reg
allocReg = liveRegs %%= \l -> if l == 0 then error "no free regs: TODO push to stack"
  else countTrailingZeros l & \r -> (toEnum r , clearBit l r)
getLiveRegs :: MkX86M [X86.Reg]
getLiveRegs = use liveRegs <&> \lv ->
  bitSet2IntList (fromIntegral (complement lv) `clearBit` fromEnum X86.RSP) <&> toEnum

valueToReg :: Value -> MkX86M Value -- Reg
valueToReg r = case r of
  Reg{} -> pure r
  StackSlot n (Bits 64) -> use stackSz >>= \sz -> if sz == 8 && n == 0
    then allocReg >>= \r -> writeAsm (X86.pop64 r) $> Reg r (Bits 32) -- hack type
    else _

mkX86F :: RetNodeF (MkX86M Value) -> MkX86M Value
mkX86F = \case
  RPNF (s : stack) instrs -> s >>= valueToReg >>= \seed -> let
    -- 2op imminstr ignores stack
    immOp (val@(Reg l _) , stack) instr (Fin 32 imm) = (,stack) <$> case instr of
      NumInstr (PredInstr pI) -> freeReg l 
        *> writeAsm (X86.cmpImm32 l (fromIntegral imm)) $> VJmpCond (getX86JmpPred pI)
      instr | Just okInstr <- getX86InstrImm32 instr -> inPlaceReg l >>= \case
        True  -> writeAsm (okInstr l (fromIntegral imm)) $> val
        False -> reassign l Nothing *> writeAsm (okInstr l (fromIntegral imm)) $> val
    -- 2op reg instr
    binOp (rVal@(Reg r _) , next : stack) instr = next >>= valueToReg >>=
      \lVal@(Reg l _) -> (,stack) <$> case instr of
      -- non-destructive
      NumInstr (PredInstr pI) -> freeReg r *> freeReg l *>
        writeAsm (X86.cmpReg32 l r) $> VJmpCond (getX86JmpPred pI)
      -- destroys lOp
      NumInstr nI  -> inPlaceReg l >>= \case
        True  -> freeReg r *> writeAsm (getX86NumInstr nI l r) $> lVal
        False -> do
          -- ! reassign args pointing here
          reassign l Nothing
          freeReg r *> writeAsm (getX86NumInstr nI l r) $> lVal
      instr -> error $ show instr
    unOp (rVal@(Reg r _) , stack) instr = (,stack) <$> case instr of
      NullString -> pure (VJmpCond X86.JZ) -- TODO

    go stack op = case op of
      ImmOp instr val -> immOp stack instr val
      BinOp instr     -> binOp stack instr
      UnOp  instr     -> unOp  stack instr
    -- stack must be fully used else internal panic
    in foldM go (seed , stack) instrs <&> \(val , []) -> val

  ArgRegF i -> use argRegs <&> (V.! i)
  SetLitF (Fin n imm) -> allocReg >>= \r -> Reg r (Bits 32) -- type hack!
    <$ writeAsm (X86.movImm32 r (fromIntegral imm))

  -- Preserve & rename registers
  CallQNameF tailCall q mkArgs {-| modName q == thisM-} -> use modBinds >>= \v ->
    liftIO (MV.read v (unQName q)) >>= \case
    (cc , Left{}) -> error ("forward ref: " <> showRawQName q) -- TODO topological sort?
    ((argCC , retVal@(Reg retReg retTy)) , Right addr) -> do
      sequence_ mkArgs
      if tailCall -- TODO clean stack, then jmp
      then use memPtr >>= \ref -> retVal <$
        writeAsm (X86.jmpImm32 (fromIntegral (minusPtr addr ref) - X86.jmpImm32Sz))
      else do
        spilledRegs <- getLiveRegs
        spilledRegs `forM_` \r -> writeAsm (X86.push r)
        ref <- use memPtr
        writeAsm (X86.callImm32 (fromIntegral (minusPtr addr ref) - X86.callRelativeSz))
        -- Its possible a different arg wanted to write to RAX/our ret-conv
        reverse spilledRegs `forM_` \r -> writeAsm (X86.pop64 r)
        setRegInUse retReg
        pure retVal

  IfElseF canRet cond ok ko -> let
    patchLabel jmpSz comeFrom ref jmpTy = writeAsmAt comeFrom
      (X86.jmpCondImm32 jmpTy (fromIntegral (minusPtr ref comeFrom) - jmpSz))
--  patchJmp comeFrom ref = writeAsmAt comeFrom (X86.jmpImm32 (fromIntegral (minusPtr ref comeFrom) - X86.jmpImm32Sz))
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

  RetF ret r -> (r >>= respectRetLoc ret) <* writeAsm X86.ret
  x -> error $ show (() <$ x)

respectRetLoc ret@(Reg retLoc _) (Reg v _) = ret <$
  (if v == retLoc then pure () else writeAsm (X86.movR64 retLoc v))

genAsm :: V.Vector CallingConv -> V.Vector Value -> Value -> Term -> MkX86M Value
genAsm ccs argVals retVal term = let
  start = (() , Top term) -- (RegMachineState (RetLoc retVal) ccs , Top term)
  in -- d_ (ana (mkRegMachineU argVals retVal False) start :: RetNode) $
    hylo mkX86F (mkRegMachineU ccs retVal False) start

-- * Convert types to asmTypes
-- * Compute Start state for function , alloc args , retloc , calling convention
-- ? using retloc registers before they are needed
getCallingConv :: Expr -> CallingConv
getCallingConv (Core bindTerm ty) = let
  sizeOfProd pr = sum (asmSizeOf <$> pr)
  tyToAsmTy (TyGround [th]) = case th of
    THPrim (PrimInt n)         -> Bits n
    THPrim (PtrTo (PrimInt n)) -> Bits 64
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
--  ProdTy prodTy@(nbits , prod) | nbits <= 64 -> let
--    nFields = BSM.size prod
--    elems   = BSM.elems prod -- BSM.elems = sorted on QNames TODO sort on sizes?
--    in unfoldrExactN' (V.length elems) allocArg (V.toList elems , freeRegs)
--      & \(v , seed) -> (VProd v prodTy , seed)
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

getRhs :: Int -> Expr -> Either Text (Term , IM.IntMap Int)
getRhs nArgs (Core term ty) = case term of
  BruijnAbs n dups body -> case compare nArgs n of
    EQ -> Right (body , dups)
    GT -> _pap
    LT -> Left $ "impossible: function has non-function type: " <> show (nArgs , n)
      <> "\n  " <> toS (prettyTermRaw term) <> "\n: " <> toS (prettyTyRaw ty)
  term | nArgs == 0 -> Right (term , mempty)
  _ -> Left $ show (nArgs , term)

-- C calling conv = ret in rax, args in rdi, rsi, rdx, rcx, r8, r9 , rest on stack in rev order
-- callee saved = r[12..15] rsp, rbp
did_LiveRegs :: Word16 -> Word16
did_LiveRegs live = trace @String (printf "%b\n" live) live

-- Setup calling convention and MkX86 initial state
bindToAsm :: ModuleIName -> V.Vector LoadedMod -> MV.IOVector (CallingConv, Either [Word32] (Ptr Word8)) -> V.Vector CallingConv -> (Ptr Word8 , Int) -> Int -> Expr -> IO (Ptr Word8)
bindToAsm thisM loadedMods mb ccs (memPtr' , memLen') bindINm expr = let
  -- Get calling convention from the function
  (argValues , retValue) = getCallingConv expr
  liveRegsStart = complement 0 `clearBit` fromEnum X86.RSP -- All Except RSP
  liveArgs = let
    setReg live (Reg r _) = clearBit live (fromEnum r)
    in V.foldl setReg (complement 0) argValues
  in case getRhs (V.length argValues) expr of
  Left e -> trace e $ pure memPtr' -- cannot generate asm for this binding
  Right (rhs , argDups) -> let
    regDups' = VU.create $ do
      mv <- MVU.replicate 16 0
      IM.toList argDups `forM_` \(i , n) ->
        MVU.write mv (argValues V.! i & \(Reg ar _) -> fromEnum ar) n
      pure mv
    startState = MkX86State
      { _memPtr = memPtr' , _memLen = memLen'
      , _modBinds = mb
      , _liveRegs = liveArgs .&. liveRegsStart -- & did_LiveRegs
      , _argRegs  = argValues
      , _regDups  = regDups' -- VU.replicate 16 0
      , _stackSz  = 0
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
  modBinds <- V.unsafeThaw (ccs <&> (, Left[]))

  startMainPtr <- X86.mkAsm' memLen memPtr
    $ concat [X86.pop64 X86.RDI , X86.pop64 X86.RSI , X86.pop64 X86.RDX]
  entryEndPtr <- X86.mkAsm' memLen startMainPtr -- memPtr
    $ concat [ X86.callImm32 0 , X86.movR64 X86.RDI X86.RAX , X86.movImm32 X86.RAX 60{-SysExit-} , X86.syscall ]

  let entrySym = [(0 , "start")]
  (endPtr , syms) <- foldM (appendBind modBinds) (entryEndPtr , entrySym) lets
  _mainEntry <- fromIntegral <$> case maybeMain of
    Nothing -> pure 0
    Just i  -> do
      mainPtr <- MV.read modBinds i <&> \(_ , Right ptr) -> ptr
      X86.mkAsm' memLen startMainPtr (X86.callImm32 (fromIntegral (minusPtr mainPtr startMainPtr) - X86.callRelativeSz))
      pure 0
  pure (endPtr , ({-mainEntry-} 0 , syms)) -- main entry is our exit syscall
  -- atm the first function of this section is the entry point
