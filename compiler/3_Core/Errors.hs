module Errors where
import CoreSyn
import ShowCore

data BiFail
  = TextMsg     Text
  | AbsentLabel QName
  | AbsentField QName
  | TyConMismatch

data TmpBiSubError = TmpBiSubError { msg :: BiFail , got :: Type , expected :: Type }
data BiSubError = BiSubError SrcOff TmpBiSubError
data CheckError = CheckError { inferredType :: Type , annotationType :: Type }
data ScopeError
  = ScopeError Text
  | AmbigBind  Text
data TCErrors = TCErrors [ScopeError] [BiSubError] [CheckError]

deriving instance Show BiFail
deriving instance Show BiSubError
deriving instance Show TmpBiSubError
