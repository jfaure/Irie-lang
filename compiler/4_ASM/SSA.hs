-- Optimized cpu form designed to be easily converted to C or llvm or wasm
-- Explicit memory read/writes

-- * Runtime fusion
-- * Reflection: Runtime beta-optimality (pap-reduce) & GPU/distribution => lib JIT ?
-- * Memory: non-fusible | duped Labels
-- * Mem-layout , label subtyping
-- * Clone Lazy-incremental

-- # Mem-layout , label subtyping , cloning
-- Labels have their own run of memory in case they need to grow (64 elems + bitset)
-- All labels could be part of a recursive type: BitSet header indicating variant element
-- Finalize: when a tree is unlinked without deleting the end
-- Header: (Duping | Linear) & Tag bitset & chunksize

-- CArray:   { Ptr , Len , (mmap | malloc | const) }
-- IrieTree: { Ptr , Len , [ Tag , elemSize ] }
-- IrieArray

{-# LANGUAGE TemplateHaskell , TypeFamilies #-}
module SSA where
import Prim
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified CoreSyn
import qualified ShowCore()
import Data.Functor.Foldable.TH (makeBaseFunctor)

type V = V.Vector

data Module = Module {
   moduleName ∷ Text
 , typeDefs   ∷ V.Vector Type
 , externs    ∷ V.Vector Function
 , locals     ∷ V.Vector Function
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
 deriving Show

data FunctionDecl = FunctionDecl {
   name  ∷ Text
 , args  ∷ [Type]
 , retTy ∷ Type
}

data Function = Function {
   fnDecl ∷ FunctionDecl
 , a0     ∷ Int
 , body   ∷ Expr
}

data Callable expr
 = LocalFn IName
 | Prim    PrimInstr
 | Op      expr  Type -- Arg or PAp or result of Switch
 deriving (Functor , Traversable , Foldable , Show)
data Expr
 = Arg    IName
 | Local  IName -- Dup
 | Extern IName
 | LitE   Literal

 | ECallable (Callable Expr)
 | Call      (Callable Expr) [Expr]
 | Switch    Expr [(Int , Expr)] Expr -- scrut alts default
 | PAp Expr  [Expr]

 | RawFields Type (V Expr) -- maybe rm
 | Struct Type (V Expr)
 | SumData (V Type) Expr Expr -- tag and value
 | Boxed Type Expr    -- malloced node

 | ROSexpr ROS   -- record-of-sum

 | Ret   Expr          -- wraps a top-level expr
 | BitCast Type Expr

 | FromPoly Type Expr
 | ToPoly   Type Expr

 | UnUnion Int Type Expr
 | Load  Type Expr
 | Gep   Type Int Expr   -- C"&(→)" Only TStruct and TSum
 | Next  Type Expr       -- C"(&t)[1]" Only TStruct and TSum
 | Index Type Int Expr   -- C"→"
 | Extract Type Int Expr -- C"."
 | Dup IName Int Expr

 | Let [(IName , Expr , Type)] Expr -- assign Args
 | Alloca Type -- for gmp
 | Void -- top | {}
 deriving Show

sumTag_t = TPrim (PrimInt 32)

builtins = V.fromList [
 ]

type Off = Expr
type ROS = V (ROSField Expr)
data ROSField expr
 = ROSFieldMem { fieldOffset ∷ Off  , sumOffset ∷ Maybe Off } -- record of sum
 | ROSFloats   { fieldFloat  ∷ expr , sumTag ∷ Maybe expr }
 deriving (Show , Functor , Foldable , Traversable)

-----------------------
-- Generation: MkSSA --
-----------------------
type CGEnv s a = StateT (CGState s) (ST s) a
data CGState s = CGState {
   wipBinds    ∷ MV.MVector s CGWIP
 , typeDef     ∷ Int -- typedef counter
 , wipTypeDefs ∷ [Type]
 , top         ∷ Bool -- for inserting Rets
 , locCount    ∷ Int
 , argTable    ∷ MV.MVector s (Expr , Type)
 , muDefs      ∷ IntMap Int
 , expectedTy  ∷ Type
 , thisMod     ∷ CoreSyn.ModIName
 }

data CGWIP
  = WIPCore  (HName , CoreSyn.Bind)
--  | WIPConst SSALiteral
  | WIPFn    Function
  | WIPDecl  FunctionDecl
  | WIPTy    IName -- index to typedef map
  deriving Show

deriving instance Show FunctionDecl
deriving instance Show Function
deriving instance Show Module

makeBaseFunctor ''Type
makeBaseFunctor ''Expr
