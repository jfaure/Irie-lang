{-# Language FlexibleInstances #-}
module ShowCore where

import CoreSyn
deriving instance Show VName
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
deriving instance Show Pi
deriving instance Show BiCast
deriving instance Show ExternVar
deriving instance Show Mixfixy
deriving instance Show Lam
deriving instance Show LamB
deriving instance Show Specialisations
