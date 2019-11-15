-- Primitives: literals and instructions
-- conversions from Prim to llvm instructions/types
-- PrimInstr are roughly equivalent to LLVM.AST. (Operand->Operand->Operand)
-- However they are more flexible and some are more powerful
module Prim
where

data Literal
 = Char Char | Int Integer | Frac Rational | String String
 | Array [Literal] -- incl. tuples
-- | WildCard      -- errors on evaluation

-----------
-- types --
-----------
data PrimType
 = PrimInt Int -- typeBits
 | PrimFloat FloatTy
 | APInt -- arbitrary precision int
 | APFloat
 | PrimArr PrimType
 | PrimTuple [PrimType]
 | PtrTo PrimType
 | PrimExtern   [PrimType]
 | PrimExternVA [PrimType]

data FloatTy = HalfTy | FloatTy | DoubleTy | FP128 | PPC_FP128

------------------
-- Instructions -- 
------------------
data PrimInstr
 = IntInstr   IntInstrs
 | NatInstr   NatInstrs
 | FracInstr  FracInstrs
 | MemInstr   ArrayInstrs
 -- TODO conversion instructions, bitcasts, bitwise ops
 -- Maybe memory instrs, va_arg, aggregate instrs, vector

data IntInstrs   = Add | Sub | Mul | SDiv | SRem | ICmp
data FracInstrs  = FAdd | FSub | FMul | FDiv | FRem | FCmp
data NatInstrs   = UDiv | URem
data ArrayInstrs = ExtractVal | InsertVal | Gep -- pointer arithmetic

deriving instance Eq PrimType
deriving instance Eq FloatTy

deriving instance Show Literal
deriving instance Show PrimType
deriving instance Show FloatTy
deriving instance Show PrimInstr
deriving instance Show IntInstrs
deriving instance Show NatInstrs
deriving instance Show FracInstrs
deriving instance Show ArrayInstrs
