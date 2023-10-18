-- Primitives: literals and instructions
-- conversions from Prim to llvm instructions/types
-- PrimInstr is a superset of LLVM.AST.Instruction
module Prim where
import Prelude hiding (show)
import GHC.Show (Show(..))

data Literal
 = Char Char
-- | I32 Int
-- | Int Integer -- convenience
 | Fin Int Integer
 | PolyInt   !Text
 | PolyFrac  !Text
 | String    [Char]
 | RevString [Char]
 | LitArray [Literal] -- incl. tuples ?
 | DirStream [FilePath] -- Unfortunately posix dirstreams are hidden so I cannot derive a binary instance for it
-- | LitTuple [Literal]
-- | WildCard      -- errors on evaluation

-----------
-- types --
-----------
data PrimType
 = PrimInt !Int -- typeBits
 | PrimNat !Int
 | PrimBigInt  -- =~ gmp int
 | PrimBigNat
 | PrimFloat !FloatTy
 | PrimArr      PrimType
 | PtrTo        PrimType
 | PrimTuple    [PrimType]
 | PrimExtern   [PrimType]
 | PrimExternVA [PrimType]
 | PrimCStruct
 | PrimStrBuf
 | POSIXTy POSIXType
 | X86Vec Int -- width: 128 , 256

data FloatTy = HalfTy | FloatTy | DoubleTy | FP128 | PPC_FP128
-- POSIXTypes require the backend to include C headers
data POSIXType = DirP | DirentP

------------------
-- Instructions --
------------------
data PrimInstr
 = NumInstr   !NumInstrs

 | MemInstr   !ArrayInstrs
 | TyInstr    !TyInstrs
 | CallExt    Text

 | MkTop | MkBot -- no-op casts

 | Zext | Sext

 | Puts | PutsN | PutChar | PutNbr

 | PowApp Int -- pow application of function
 | MkTuple
 | MkPAp Int
 | StrToL
 | IfThenE
 | ExprHole   -- errors on eval, but will typecheck
 | MkNum      -- instantiation must happen via function call
 | MkReal
 | AddOverflow
 | Alloc
 | Len -- len of PrimArray
 | SizeOf
 | Ptr2Maybe -- glue between ptr/nullptrs and algebraic data (usually Maybe t = [Nothing | Just t])
 | UnfoldLStack

 -- conversion between primitive arrays and ADTs
 -- ? Should Maybe be a builtin type for unfolding purposes
 | UnFoldStr -- (Seed → (Bool , A , Seed)) → Seed → %ptr(A)
 | NextElem  -- %ptr(A) → (A , %ptr(A))
 | ToCStruct | ToCStructPacked | FromCStruct | FromCStructPacked

 | UnCons     -- pop a pointer (should test NullString first)
 | NullString -- test if str is null

 | AllocStrBuf
 | PushStrBuf
 | StrBufToString

 | NewArray
 | WriteArray
 | ReadArray

 -- Posix instructions
 | GetCWD
 | ReadFile
 | WriteFile
 | Execve
 | Fork
 | TraceId

 -- Almost Posix
 | OpenDir
 | ReadDir
 | IsDir -- check if a DIRP ptr is not null

 -- Posix glue
 | DirentName -- extract name from dirent struct

data NumInstrs
 = IntInstr   !IntInstrs
 | PredInstr  !Predicates
 | NatInstr   !NatInstrs
 | BitInstr   !BitInstrs
 | FracInstr  !FracInstrs

 -- type instructions
data TyInstrs
 = MkIntN  -- : Nat → Set --make an int with n bits
 | Arrow   -- : Set → Set

-- TODO conversion instructions, bitcasts, Maybe va_arg, SIMD
data Predicates  = EQCmp | NEQCmp | GECmp | GTCmp | LECmp | LTCmp | AND | OR
data IntInstrs   = Add | Sub | Mul | SDiv | SRem | Neg | AbsVal | IPow | Ord | Chr
data NatInstrs   = UDiv | URem | UDivMod
data BitInstrs   = And | Or | Not | Complement | Xor | ShL | ShR | BitRev | ByteSwap | PopCount | CTZ | CLZ | FShL | FShR | RotL | RotR | TestBit | SetBit
                 {- BMI1 -} | ANDN | BEXTR | BLSI | BLSMSK | BLSR| CtTZ {- BMI2 -} | BZHI | MULX | PDEP | PEXT
data FracInstrs  = FAdd | FSub | FMul | FDiv | FRem | FCmp
data ArrayInstrs = ExtractVal  -- | InsertVal | Gep

primInstr2Nm = \case
  NumInstr i -> show i
  TyInstr  i -> show i
  i          -> show i
-- MemInstr   !ArrayInstrs

isAssoc = \case
  NumInstr (IntInstr i) -> case i of { Add->True ; Mul->True ; _ -> False }
  _ -> False

isCommutative = \case
  NumInstr (IntInstr i) -> case i of { Add->True ; Mul->True ; _ -> False }
  _ -> False

arity = \case
  NumInstr u -> 2
  NullString -> 1

deriving instance Show Literal
deriving instance Show PrimType
deriving instance Show FloatTy
deriving instance Show PrimInstr
deriving instance Show TyInstrs
deriving instance Show IntInstrs
deriving instance Show BitInstrs
deriving instance Show NatInstrs
deriving instance Show FracInstrs
deriving instance Show ArrayInstrs
deriving instance Show Predicates
deriving instance Show NumInstrs
deriving instance Show POSIXType

deriving instance Ord Literal
deriving instance Ord PrimType
deriving instance Ord FloatTy
deriving instance Ord PrimInstr
deriving instance Ord TyInstrs
deriving instance Ord IntInstrs
deriving instance Ord BitInstrs
deriving instance Ord Predicates
deriving instance Ord NatInstrs
deriving instance Ord FracInstrs
deriving instance Ord ArrayInstrs
deriving instance Ord NumInstrs
deriving instance Ord POSIXType

deriving instance Eq Literal
deriving instance Eq PrimType
deriving instance Eq FloatTy
deriving instance Eq PrimInstr
deriving instance Eq IntInstrs
deriving instance Eq BitInstrs
deriving instance Eq Predicates
deriving instance Eq NatInstrs
deriving instance Eq FracInstrs
deriving instance Eq ArrayInstrs
deriving instance Eq TyInstrs
deriving instance Eq NumInstrs
deriving instance Eq POSIXType

prettyPrimType :: PrimType -> Text
prettyPrimType = toS . \case
  PrimInt x        -> "%i" <> show x
  PrimBigInt       -> "%BigInt"
  PrimNat x        -> "%ui" <> show x
  PrimFloat f      -> "%f" <> show f
  PrimArr prim     -> "%@[" <> show prim <> "]"
  PrimTuple prim   -> "%tuple(" <> show prim <> ")"
  PtrTo t          -> "%ptr(" <> show t <> ")"
  PrimExtern   tys -> "%extern(" <> show tys <> ")"
  PrimExternVA tys -> "%externVA(" <> show tys <> ")"
  POSIXTy t -> case t of { DirP → "%DIR*" ; DirentP → "%dirent*" }
  PrimCStruct -> "%CStruct" -- (" <> show x <> ")"
  PrimStrBuf -> "%StrBuf" -- (" <> show x <> ")"
  X86Vec i -> "__m" <> show i
  x -> error $ show x

primSubtypeOf :: PrimType -> PrimType -> Bool
PrimInt a `primSubtypeOf` PrimInt b = a <= b
PrimNat a `primSubtypeOf` PrimNat b = a <= b
x `primSubtypeOf` y = x == y
