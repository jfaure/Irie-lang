-- Optimized cpu form ready to be converted 1:1 to C or llvm
module SSA where
import Prim
import qualified Data.Vector as V

type V = V.Vector

data Module = Module {
   moduleName :: Text
 , typeDefs   :: V.Vector Type
 , externs    :: V.Vector Function
 , locals     :: V.Vector Function
}

data Type
 = TPrim     PrimType
 | TStruct   Int (V Type) -- typedef name
 | TTuple        (V Type) -- no typedef
 | TSum      Int (V Type) -- i is index of largest alt
 | TFunction (V Type) Type
 | TPoly
 | TRec Int      -- Int points to the types typedef

-- | TypeDef Type Int -- typeDefs vector
 | TGMPInt
 | TGMPFloat
 | TVoid -- no ty

data FunctionDecl = FunctionDecl {
   name :: Text
 , args :: [Type]
 , retTy:: Type
}

data Function = Function {
   fnDecl :: FunctionDecl
 , a0     :: Int
 , body   :: Expr
}

data Callable
 = LocalFn IName
 | Prim    PrimInstr
 | Op      Expr  Type -- Arg or PAp or result of Switch
data Expr
 = Arg    IName
 | Local  IName -- Dup
 | Extern IName
 | LitE   Literal

 | ECallable Callable
 | Call      Callable [Expr]
 | Switch    Expr [(Int , Expr)] Expr -- scrut alts default
 | PAp Expr  [Expr]

 | RawFields Type (V Expr) -- maybe rm
 | Struct Type (V Expr)
 | SumData (V Type) Expr Expr -- tag and value
 | Boxed Type Expr    -- malloced node

 | Ret   Expr          -- indicate top-level expr
 | BitCast Type Expr

 | FromPoly Type Expr
 | ToPoly   Type Expr

 | UnUnion Int Type Expr
 | Load  Type Expr
 | Gep   Type Int Expr   -- C"&(->)" Only TStruct and TSum
 | Index Type Int Expr   -- C"->"
 | Extract Type Int Expr -- C"."
 | Dup IName Int Expr

 | Let [(IName , Expr , Type)] Expr -- assign Args
 | Alloca Type -- for gmp
 | Void -- top | {}

sumTag_t = TPrim (PrimInt 32)

builtins = V.fromList [
 ]

deriving instance Show Expr
deriving instance Show Callable
deriving instance Show FunctionDecl
deriving instance Show Function
deriving instance Show Type
deriving instance Show Module
