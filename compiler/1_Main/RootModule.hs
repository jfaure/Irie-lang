module RootModule where
import CoreSyn
-- Main = anaM parse > apoM scope (cata unpat) > cataM infer > apo(M) β

-- # Modules:
-- * sigs
-- * fn of their dependencies (how to walk dep graph?)
-- * appendable (esp. for repl)
-- * updateable (adding specs , user updates)
-- * searchable (fuzzy search on types , names)
-- * module-mutuality (can cat-files and get a valid multi-module module?)
-- * writeable (cache)
-- * modular (handle HNames + cross-module translations)

-- GlobalResolver : modCount , modNameMap , globalNames , lnames , allBinds , globalMixfixWords
-- Externs = extNames : [ExternVar] , extBinds : [[(HName , Expr)]] , importLabels , modNamesV
-- QName = ModName , BindName

------------
-- Driver --
------------
data CFatal = NoFile Text | ParseFail Text | JudgeFailFatal Text
data CompileError = Fatal CFatal -- | Errors [_]

type Compiler a = IO (Either CompileError a)
