module CoreBinary where
import MixfixSyn
import CoreSyn
import Prim
import Data.Binary
import Data.Vector.Binary()

deriving instance Generic VName
deriving instance Generic QName
deriving instance Generic Term
deriving instance Generic LensOp
deriving instance Generic (TyCon Type)
deriving instance Generic TyHead
deriving instance Generic Type
deriving instance Generic Bind
deriving instance Generic JudgedModule
deriving instance Generic Expr
deriving instance Generic BiSub
deriving instance Generic Kind
deriving instance Generic Pi
deriving instance Generic BiCast
deriving instance Generic ExternVar
deriving instance Generic QMFWord
deriving instance Generic Mixfixy
deriving instance Generic MixfixDef
deriving instance Generic Prec
deriving instance Generic Assoc
deriving instance Generic LetMeta
deriving instance Generic OptBind

-- Prim
deriving instance Generic Literal
deriving instance Generic PrimType
deriving instance Generic FloatTy
deriving instance Generic PrimInstr
deriving instance Generic IntInstrs
deriving instance Generic Predicates
deriving instance Generic NatInstrs
deriving instance Generic FracInstrs
deriving instance Generic ArrayInstrs
deriving instance Generic TyInstrs
deriving instance Generic BitInstrs
deriving instance Generic NumInstrs
deriving instance Generic GMPSpecial
deriving instance Generic POSIXType

instance Binary VName
instance Binary QName
instance Binary Term
instance Binary LensOp
instance Binary (TyCon Type)
instance Binary TyHead
instance Binary Type
instance Binary Bind
instance Binary JudgedModule
instance Binary Expr
instance Binary BiSub
instance Binary Kind
instance Binary Pi
instance Binary BiCast
instance Binary ExternVar
instance Binary QMFWord
instance Binary Mixfixy
instance Binary Prec
instance Binary MixfixDef
instance Binary Assoc
instance Binary ArgShape
instance Binary LetMeta
instance Binary OptBind

-- primitives
instance Binary Literal
instance Binary PrimType
instance Binary FloatTy
instance Binary PrimInstr
instance Binary IntInstrs
instance Binary Predicates
instance Binary NatInstrs
instance Binary FracInstrs
instance Binary ArrayInstrs
instance Binary TyInstrs
instance Binary BitInstrs
instance Binary NumInstrs
instance Binary GMPSpecial
instance Binary POSIXType
