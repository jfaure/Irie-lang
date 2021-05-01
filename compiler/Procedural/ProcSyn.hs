module Procedural.ProcSyn where
import CoreSyn

type Module   = [Symbol]
type QTT      = Int
type Record a = IntMap (a , QTT)
type Sum a    = IntMap a

data Function = Callable Args Expr
type Args = (Record ValType) -- <0 fields = normal arguments
data Callable
 = FnPtr
 | PrimInstr Instr
 | PAp Callable Int [Val] -- number of known args

data Addr = Addr [FName] Val
data SplitTree = SplitTree (IntMap Function) | Alloc
data Alloc = Alloc Int -- frame pointer , shared overlay
data LensOp = Get | Set | Over
type RecordResolver = Vector Int -- record subtyping

data ValType = Lit | Addr | Record | RecordView | SumData | Case | Poly | Switch
data Val -- irreducible; can pass as is to functions
  = Arg Int ValType -- ValType is crucial information
  | Lit
  | Fn Function
  | Cons IntMap [Val]
  | Splitter SplitTree

-- locals are appended to the argRecord
data Expr -- requires computation (except V)
  = V Val
  | App [Expr] Expr

  -- Sum data
  | Label [Expr] Alloc -- Generator (avoid inst recursion) ?
  | PreSplit [Expr] SplitTree -- can fold-build the label

  -- record
  | Lens LensOp Addr
  | Write Addr Val Expr -- Expr is next thing to evaluate
  | Read  Addr Val Expr

data AllocFns = MergeFrames | ShareFrame | FreeFrame | NewFrag | FreeFrag | PushFrag | PopFrag

-- Notes
-- We don't use fn args or cpu registers at this stage.
-- The argrecord (basically custom stack) is used as much as possible
-- Label: splitters are preffered, note parallel splits (eg. zip) not worth it
-- Record: writes/reads are appended to the argRecord

-- Tail calls:
-- outer labels can be PApped write heap instead of stack
-- outer cases can be sent inwards (split-tree)

-- Memory:
-- argstack is main record used for allocating most records / small fields

-- ?
-- QTT on fields / addresses
-- tail call / hylomorphism
-- call stack fork
-- shared overlay for writing to shared data
-- buffer (rev / array)
-- distribute (share streams)
-- zip        (combine streams); multisplit
-- generator vs split-tree
