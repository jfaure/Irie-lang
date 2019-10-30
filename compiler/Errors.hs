module Errors
where

-- TypeJudge --
data TypeError
 = ArityMismatch
 | AliasLoop
 | SubsumptionFailure
 | CallNonFunction

data InternalError
 = UntypedPrimitive
 | NoInferFn

-- ToCore --
data SemanticsError
 = UnknownTyName
 | UnknownClassFn
 | BadInstanceDecl
 | InstanceUnknownClass
 | NotInScope
