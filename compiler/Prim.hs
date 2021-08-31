-- Primitives: literals and instructions
-- conversions from Prim to llvm instructions/types
-- PrimInstr is a superset of LLVM.AST.Instruction
module Prim where
import Prelude hiding (show)
import GHC.Show (Show(..))

data Literal
 = Char Char
 | Int Integer -- convenience
-- | Frac Rational
 | PolyInt   !Text -- gmp
 | PolyFrac  !Text -- gmp
 | String    [Char]
 | Array [Literal] -- incl. tuples ?
-- | Tuple [Literal]
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
 | PrimArr   PrimType
 | PtrTo     PrimType
 | PrimTuple [PrimType]
 | PrimExtern   [PrimType]
 | PrimExternVA [PrimType]

data FloatTy = HalfTy | FloatTy | DoubleTy | FP128 | PPC_FP128

------------------
-- Instructions -- 
------------------
data PrimInstr
 = NumInstr   !NumInstrs
 | GMPInstr   !NumInstrs

 | MemInstr   !ArrayInstrs
 | TyInstr    !TyInstrs
 | CallExt    Text

 | MkTop | MkBot -- no-op casts
 
 | Zext | Sext
 | GMPZext Int | GMPSext Int -- take an i<64 to a gmp integer

 | Puts | PutNbr | GMPPutNbr

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

data NumInstrs
 = IntInstr   !IntInstrs
 | PredInstr  !Predicates
 | NatInstr   !NatInstrs
 | BitInstr   !BitInstrs
 | FracInstr  !FracInstrs

 -- type instructions
data TyInstrs
 = MkIntN  -- : Nat -> Set --make an int with n bits
 | Arrow   -- : Set -> Set

 -- TODO conversion instructions, bitcasts, Maybe va_arg, SIMD
data Predicates  = EQCmp | NEQCmp | GECmp | GTCmp | LECmp | LTCmp
data IntInstrs   = Add | Sub | Mul | SDiv | SRem | Neg | AbsVal | IPow
data NatInstrs   = UDiv | URem
data BitInstrs   = And | Or | Not | Xor | ShL | ShR | BitRev | ByteSwap | CtPop | CtLZ | CtTZ | FShL | FShR | RotL | RotR
data FracInstrs  = FAdd | FSub | FMul | FDiv | FRem | FCmp
data ArrayInstrs = ExtractVal | InsertVal | Gep

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

primSubtypeOf :: PrimType -> PrimType -> Bool
PrimInt a `primSubtypeOf` PrimInt b = a <= b
PrimNat a `primSubtypeOf` PrimNat b = a <= b
x `primSubtypeOf` y = x == y
