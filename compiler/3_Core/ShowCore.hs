module ShowCore where

import CoreSyn

-- instance Show VName where show = prettyVName
-- instance Show Term where show = prettyTerm
-- instance Show TyHead where show = prettyTyHead
-- instance Show Bind where show = prettyBind
--deriving instance Show QName
deriving instance Show VName
deriving instance Show Term
deriving instance Show LensOp
deriving instance Show TyCon
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
