module MachineCode where
import Prelude hiding (Ptr)
import Prim
import Data.Vector as V
import CoreSyn
type V = V.Vector
type LName = Int -- TODO

-- ## New revelations
-- * cap fields/labels to 64
--   => use pdep to mark frets for subtyping casts
--   => can inc. limit using a tree if necessary

-- ## MachineCode
--  * eliminate Trees : flatten all data to Tuples up to recursion & lift all tags
--  * SOA form for data
--  * eliminate polymorphism
--  * Insert memory handling
--  * β-optimality
--  * SIMD + multithread
--  ? Wrap = Tuple + tag (? should products lift all tags)
--  ? Extract + split lists of tuples

-- ## ?? Encode rec-structure
-- * D = distinct branch factors (statically known , incl. 0 for leaf)
-- * perfect tree of d-indexes. sz = D ** max depth
-- * RLE each branch
-- rec = (depth , ptree) : D
-- eg. 1 (2 (0) (0)) =

-- * Subtype
-- label promotion
-- sumtypes
-- record
-- erased lambdas
-- tycon trees

data MType
  = TPoly
  | TAtom PrimType
  | TProd (V MType) -- Tuples: Fully flattened
                    -- sorted fields on size first (to pack booleans etc..) then lexicographically on field names
  | TSum (V MType)
  | TTree { branchFactor :: Int -- extract recursives
          , dataArrays   :: V MType }  -- 0 for Peanos / enums (but also subtree data-array always present)

-- ! Tree insertion + deletion + modify + sum subtyping (adding space for excess labels) + rec->norec sub
-------------------------------------------------
-- Simulation for builtin runtime tree operations
-------------------------------------------------
-- v passdown frame (rec-pointers)
-- arg = { tag : int ; datum : DATUM ; recholes : V (recFactor , size , dataPtr : [DATUM]) }
-- cons TAG TREETYPE args = case recholes <$> args of
--   [] -> mkRecord TAG args
--   r0 : rs -> if r0.tag == TAG
--     then pushRLE r0.rle (mkRecord args) (mkPtrs rs) -- allocate new rle if == 0 || >= rlesz
--     else mkPtrs (endRLE r0) rs -- spawn ptrs to other branches and trim their rles
-- 
-- -- ? how to accept smaller than max sz tag-tree
-- match :
-- match scrut LAMS = let
--   cgLam (LamB n body) = _ -- any binds onto erase (esp. rec subtrees) can free immediately
-- --alts = lams <&> cgLam
--   in _

-- FEnv identified optimisable patterns
search   = _
lensGet  = _
lensOver = _

-- eg. [ Lit Int | Op r | BinOp r r ] => @Int + Peano BigInt indicating structure
-- BinOp (Lit 3) (Op (Lit 2)) = 2 0
-- ? 2 [  0 [ _  _ ] 1 [ _   0] ] Perfect tree of bittags (max depth * max branchFactor)

data Atomic = Lit Literal | Ptr MemPtr | Arg IName | Local IName | Top IName
data Val
 = Atom Atomic
 | Tuple (V.Vector Atomic)

data SSAU -- Static single assignment and use
 = AllocMem Atomic -- Only recursive data is written to memory
 | Node Val
 | ReadIdx SSAU Idx | WriteIdx SSAU Idx
 | Push MemPtr Atomic | Pop MemPtr
 | SI PrimInstr [Atomic] -- | SIMD PrimInstr
 | Call Atomic [SSAU]
type MemPtr = SSAU
type Idx    = SSAU

mcFunction arg body = _
-- 1. Flatten all types & tycon operations -> {} []
-- 2. Track MC types throughout expr traversal

mcTerm :: _Frame -> Term -> SSAU
mcTerm fr = \case
  Label l args -> _
    -- | New label not contained within
    -- | Recursive label
  CaseB scrut t alts def -> _

  Cast c v -> case c of
    CastProduct nDrops newFieldAndCasts -> _
--  CastSumT ->
