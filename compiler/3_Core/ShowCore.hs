{-# Language FlexibleInstances #-}
module ShowCore where
import CoreSyn
deriving instance Show VQBindIndex
deriving instance Show Term
deriving instance Show LensOp
deriving instance Show (TyCon Type)
deriving instance Show TyHead
deriving instance Show Type
deriving instance Show Bind
deriving instance Show JudgedModule
deriving instance Show Expr
deriving instance Show BiSub
deriving instance Show Kind
deriving instance Show BiCast
deriving instance Show ExternVar
deriving instance Show Mixfixy
deriving instance Show LetMeta
deriving instance Show OptBind
