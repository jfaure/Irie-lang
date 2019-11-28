module CodegenRuntime
where

import StgSyn

import LLVM.AST
import LLVM.IRBuilder.Module
import LLVM.IRBuilder.Monad
import qualified LLVM.AST.Constant as C

import qualified Data.Map.Strict as Map
import Control.Monad.State
import Control.Monad.Fix (MonadFix)
import Data.Functor.Identity (Identity)

-- ******************************************
-- * Semantics of code gen :: STG -> LLVMIR *
-- ******************************************
-- codegen happens within llvm-hs-pure ModuleBuilder and IRBuilder monads.
-- StgCase uses mdo (MonadFix) to generate phi blocks
-- stgToIR also relies on a MonadState StgToIRState
type CodeGenModuleConstraints m =
 ( MonadState StgToIRState m
 , MonadModuleBuilder m
 , MonadFix m)
type CodeGenIRConstraints m =
 ( CodeGenModuleConstraints m
 , MonadIRBuilder m)

-- ****************
-- * StgToIRState *
-- ****************
data Symbol
  = ContLi LLVM.AST.Operand -- an SSA (a global / constant)
  | ContFn LLVM.AST.Operand -- llvm function
  | ContRhs StgRhs    -- Placeholder (we can let-bind this immediately)
 -- ContPrim: llvm instruction
 -- + function wrapper (if it's used as an argument)
  | ContPrim StgPrimitive [StgType] StgType (Maybe LLVM.AST.Operand)

type TypeMap    = Map.Map StgId StgType
type SymMap     = Map.Map StgId Symbol
type DataFnsMap = Map.Map StgId DataFns

-- StackMem: this record is only used while codegenning functions returning data
-- Idea is to provide them with memory on the last stack frame that uses the data
-- recursive data is on the heap, frames must call destructors to clean these
data StackFrame = StackFrame
  { stackMemSize :: C.Constant -- How many (alloca) bytes needed by fns
  , stackMem     :: StgSsa     -- Pointer to alloca from caller's stack frame
  , destrQueue   :: [(StgFn, StgSsa)] -- destructors to call
  }

-- Note. this is used in DataFnsMap (with StgId), so these are all named that way
data DataFns = DataFns -- llvm fns generated when data is defined
  { staticSize :: C.Constant  -- normally alloca memory: sizeof data (not incl. subdata)
  , construct  :: StgFn       -- llvm packing fn to fill the struct
  , decon      :: [StgId]     -- The order of named elements in the data
  , destruct   :: Maybe StgFn -- recursive data must recursively free
  }

  | SumCon DataFns -- the type this sumConstructor constructs
           Int     -- tag number of this alternative

 -- ProxyDataFn: returns data by calling a constructor at some point
 -- This just means it needs memory from a higher stack frame
  | ProxyDataFn C.Constant    -- size needed
                StgFn

-- note. constructors are stored in dataFnsMap
-- stackFrames: some frames are responsible for stgdata.
data StgToIRState = StgToIRState 
  { bindMap    :: SymMap      -- vanilla fns/globals in scope
  , dataFnsMap :: DataFnsMap  -- basic info about a data
  , typeMap    :: TypeMap     -- Type aliases
  , tupleMap   :: Map.Map [LLVM.AST.Type] DataFns
  , stackFrame :: Maybe StackFrame -- for fns returning data - only top layer data,
  , subData    :: Bool             -- nested constructors use malloc
  }
