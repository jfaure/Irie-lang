-- Syntax designed to incrementally simplify to an asm/C like language
-- This gives us more flexibility in which simplifications to apply
-- good for printing supporting backends between Irie and asm
module Procedural.ProcSyn where
import Prim
import CoreSyn
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV

type Sz       = Int
type Module   = [Symbol]
type Record a = IntMap (a , QTT)
type Sum a    = IntMap a

-- Functions have 2 stages:
-- 1. Complicate; generate local variables and share data around
-- 2. Reduce; deallocate and return
data Function = Function {
   fn        :: Callable
 , recursive :: Bool
 , recData   :: Bool -- It returns recursive data
 , args      :: (V.Vector Arg , IntMap Arg) -- position args and free variables
 , body      :: Compute
}
type Arg = (QTT , ValType)
data Callable
 = FnPtr
 | PrimInstr PrimInstr
 | PAp Callable (V.Vector (Maybe Val)) -- args given to the pap

data SumTypes = Enum | Array { rank :: Int } | Tree

data ValType
  = Basic | If
  | RecordView -- offset list ?! shared data within
  | Labeled | Split -- args labelled only (ie never split) are worth knowing about
  | Poly -- like labels, size is variable (particularly annoying when contained in records)
         -- instantiate with Sumdata + QTT etc ?!

type CaseAlts = IntMap Function
data Val -- irreducible / trivial operations
  = Arg   Int ValType
  | Lit   Literal
  | Addr  [IField]
  | Fn    Function
  | Cons  (IntMap Val)

data Compute -- non trivial operations
  = V Val
  | App Compute [Compute]
  | Branch Val (V.Vector Compute) -- ~ if on literals (sharing may be dependent on branching !)
  | Lens LensOp Val

  | Label ILabel [Compute] -- Generator. note. foldl vs foldr
  | Splitter (V.Vector CaseAlts)   -- can split Multiple args simultaneously; (higher rank fusion)

data AllocFns = MergeFrames | ShareFrame | FreeFrame | NewFrag | FreeFrag | PushFrag | PopFrag
data DataDir = NoRec | Inward | Outward | Both -- direction of recursion (foldl vs foldr)

data CGState s = CGState {
   tailSplit :: Maybe Val
 , locals    :: MV.MVector s Val
}
type CGEnv s a = StateT (CGState s) (ST s) a

-- Sum types can contain any combination of these alt types !
-- The theme here is to exploit potential for 1 implicit pointer (via array) in each alt.
data MemorySumAlt
 = Enum
 | Peano   Int    -- contains only itself (n times)
 | Wrapper Sz     -- container (<  0 size) (primtypes, tuples, quants)
 | Array   Sz     -- container (<= 0 size) and itself 
 | Tree    Sz Int -- container (<= 0 size) and itself (1 + n) times
-- Asm:
-- Enum    => Tag
-- Peano   => Int (peano numeral)
-- Wrapper => { Tag , %iSz }
-- Array   => @ { %iSz }
--   A buffered linked list
-- Tree    => @ { &iSz , @ Ptr }
--   Can be flattened left-wise

data SumData
 = Raw (IntMap SumAlt)
 | Generator Generator

data Generators
 = Idot -- [0..]
 | Unfold Fn    | UnfoldR Fn
 | Construct Fn | ConstructR Fn
 | Map   Fn Generator -- (incl lookup on physical arrays via Idot and PAp)
 | ZipN  [Generator] 
 | Join  Generator Generator
 | Slice Int Int Generator
-- Reverse = Either Generator can do it or Manifest entire array (must not be infinite)

-- Note. Fn = | Instr table | PAp | raw fnptr
-- Splitters: (Memory | Sharing) & Generators
--   Either give splitter to generator | Give generator to splitter
-- x A. struggles with multisplitters
--   B. More natural; Generator can handle Sharing personally via buffers / tracking requests
-- ? merge (Generator -> Generator)
-- Identify--
--   foldr / foldl
--   lockstep splitters (zipWith)

-- Generator : { State , Fn }

-- Sharing: fns have to assume the worst!
--   | Extra labels for sharing cases (indicate not owned memory in place immediately)
--   | frame in front of data for sharing info |  (pointer alignment = free boolean)
--   Duped data: headers indicating regions of parent data not owned

-- General Notes for ASM strategy
-- At this stage, we don't use fn args (~= cpu registers) in favor of argrecord
-- exported functions forfeit some optimizations
-- try very hard to make tail-calls possible
-- Labels when built are handed a (single-step) splitter / allocator;this ST is private and can modify itself as it consumes labels
-- Single use data should organise a tail call to its constructor
-- Fns are responsible for their args

-- Art of Flattening; sometimes we have to comit data to memory
-- at least one pointer can always be implicit
-- tree data flattened depth first
-- Overlay (the -1 label) for sharing / extracting implicit pointers
-- Types =
--  | Peano  -- Only empty tuples in each branch
--  | Array  -- Only one size type: equisize cells (or pointers) layed out in a tensor
--  | Zipper -- Array with non-equisized cells (but predictable along a dimension)
--  | Tree   -- (Flatten depth first): Array with subsequent unpredictables as pointers
--  Note. Tree types include containers with unpredictable containement sizes
--  Note. some branches of sum types considered too large for us to grow all cells become pointers
--
-- Data frames:
-- allocator metadata
-- maybe share index
-- need to keep a ref while splitting/labelling data within the frame

-- Label:
-- OnLabel : [SplitFn Callable | rawST [Callable] | Allocator Frame]
-- gen : customState -> st_or_alloc -> Bool -- allocator or st handles the output
-- recursion;
-- PrimLabel: no recursion
-- PrimCase:  no recursion
-- AtLabel:  Array indexed generator

-- outLabel: label contains recursively generated (lazy) data
-- inlabel:  label is fully evaluated before recursion
-- outCase:  can tail call the recursion step (foldl)
-- inCase:   needs to open all labels before evaluation (foldr)

-- perfect = outLabel > inCase (foldr), inLabel > outCase (foldl)
-- otherwise = try to reverse one | have to allocate
-- ?? effects an linearisation

-- ! combine Onlabels / recursive onlabels (splitters in the splitfns)
-- => fn to mutate the ST
-- foldr f start = \case of { Next x xs => f x (foldr f start xs) ; Null => start }
-- foldr = rawST [
--   f x (foldr f start xs) -- splitting an inner label; lift to top level; needs access to generator
--   const start
--   ]

-- Recursive Labellers are always generators (must be called one step at a time)
-- eval to buffer: for (int x = 0; x < BufSZ || generator(state , splitter_or_allocator); ++x);

-- Shared data: (must be dynamically checked (fns have to assume the worst))
-- can use pointer alignment for a free boolean, and a frame in front of the data if shared info needed
-- This means that only splitter fns cause sharing
-- { FramePtr , Data + alignment boolean }
-- Shared overlay:
--   (-1) label indicates a split node (ie. where the sharing stops).
--   split node = array of nodes. master frame knows the right index

-- zippers : rank 2 arrays : 
-- pull|push through narrowest point. (pull if zipping ; push if sharing ; push if both)
-- Record resolvers: [0..n] -> IntMap -> Addr (provide external table for external record/labels)
-- ArgRecord :: flat list of pointers ; many will be sent to registers instead

-- Fns:
-- Instr table , PAps , raw Fnptrs (can use 2 bits of pointer alignment)

-- Memory:
-- argstack is main record used for allocating most records / small fields

-- Case studies:
-- zip

-- ?
-- leaf casts
-- reuse holes in argrecord / let llvm spill regs to stack
-- QTT on fields / addresses
-- tail call / hylomorphism
-- shared overlay for writing to shared data
