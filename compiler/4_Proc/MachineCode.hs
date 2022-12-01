module MachineCode where
import Prim
import Data.Vector as V
type V = V.Vector

-- ## MachineCode
--  * eliminate Trees : flatten all data to Tuples up to recursion & lift all tags
--  * SOA form for data
--  * eliminate polymorphism
--  * Insert memory handling
--  * explicit free-vars + β-optimality
--  * SIMD

-- * single argument: concatenate args into a tuple (backends should explode this later)
-- * Maybe tag register
-- * poly: either raw or pointer if too big
-- * recursive datas => flatten
-- * recursive sumdata = tag + head + Array
-- * extra (>1) rec branches become pointers
-- ? unknown sizes when flattening tuples => separate array? + size variable
mcFunction arg body = _

data MType = TPoly | TAtom PrimType | TSum (V MType) | TProd (V MType)
data Atomic = Lit Literal | Ptr MemPtr | Arg IName | Local IName | Top IName
data Expr
 = Atom Atomic
 | Tuple (V.Vector Atomic)

data SSAU -- Static single assignment and use
 = AllocMem Atomic -- Only recursive data is written to memory
 | Node Expr
 | ReadIdx SSAU Idx | WriteIdx SSAU Idx
 | Push MemPtr Atomic | Pop MemPtr
 | SI PrimInstr [Atomic] -- | SIMD PrimInstr
 | Call Atomic [SSAU]
type MemPtr = SSAU
type Idx    = SSAU
