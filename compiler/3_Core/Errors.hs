module Errors where
import CoreSyn
import ShowCore

data TmpBiSubError = TmpBiSubError { msg :: Text , got :: Type , expected :: Type }
data BiSubError = BiSubError SrcOff TmpBiSubError
data CheckError = CheckError { inferredType :: Type , annotationType :: Type }
data ScopeError
  = ScopeError Text
  | AmbigBind  Text
data TCErrors = TCErrors [ScopeError] [BiSubError] [CheckError]

deriving instance Show BiSubError
deriving instance Show TmpBiSubError
