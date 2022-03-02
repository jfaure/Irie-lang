{-# Language TemplateHaskell #-}
module FusionEnv where
import CoreSyn
import ShowCore()
import qualified Data.Vector.Mutable as MV
import qualified Data.IntMap as IM
import qualified Data.Vector as V
import Control.Lens

-- Fusion: extremely aggressively attempt to bring eliminations in contact with introductions
-- # Prep phase
-- eliminate data fixpoints => Stream / Cata / Build
-- Identify small functions which we intend to always inline
-- Identify 'CaseArgs' (when (partially) constant, folds a branch)
-- lift Case-args to top "let-binds", to avoid traversing entire expr

-- # Elimination phase
-- Proceed top-down pushing constants and constant labels inwards
-- eg. go z x@(Right ys) => if x is caseArg => inline go and fuse the case
--
-- case-of-label: constant fold
-- case-of-case : push outer case into each branch => many case-of-label
-- case-of-arg:
--   ConSpec => calls to F use a constant constructor on arg
-- case-of-(App arg _):
--   Want an arg that produces a constant label:
--     !Not all arguments to arg need to be constant for this to be fusable
--     Need to inline F into call-sites (partial specialisation | static arg)

-- # Other improvements
-- case-merge: extract sub-cases that scrutinize the same variable
-- case-liberate: unroll rec fns once to avoid repeated case on free-vars
-- -spec-constr:  specialise recursive functions once a case becomes redundant
-- Multi-if-folding: `case x - 10 of { 10 -> _ }` => `case x of { 20 -> _ }`

-- # Unboxed values
-- always-inline small functions
-- Lambda-of-Con: dup lambda to avoid duping args: (?!)
--   `\b => (f b , g b)` => `(\b0 => f b0 , \b1 => g b1)`
-- Mutuals: perhaps can make a double loop

-- Derivation
-- 1. try distrubute the id cata accross the case, then make a single cata
-- 2. else immediately make a cata, then fuse the outer cata (higher-order fusion);
-- * cata-build needs to handle all nil/cons identically, /= (tail (last) or foldr1 (first))
-- * catas from fns with same shape as the recursive type
-- ? inherited attributes / second order

-- Dynamic deforestation (multiple builds for right/left or both)
-- buildFn = (a->b->b) -> b -> b
-- List a = | Nil | Cons a (List a) | Build (R|L|B) buildFn buildFn
-- foldr k z (Build g) = g k z

-- Cases (Cata can fuse with everything, since builds are always deriveable)
-- stream (unStream s) = s
-- cata f z (build g)  = g f z (syntax translation (label -> Fn))
-- stream Build     syntax translation (label -> label)
--
-- First order (no inherited attribute) Stream / Foldr can be used interchangeably
-- Commutative and Associative folds/stream can be reversed
-- fold f        -> Stream
-- Stream next z -> fold

-- Stream derivation
-- case on lists => next s ; Cons to result => Yield ; call => Skip s2
-- when the stream producer unknown, push as a dynamic choice inside the stream

-- Stream a = ∃s. Stream (s → Step a s) s
-- Step a s = | Done | Skip  s | Yield s a
--
-- stream :: [a] -> Stream a
-- stream xs0 = Stream (\case { [] => Done ; x : xs => Yield x xs }) xs0
-- unstream :: Stream a -> [a]
-- unstream (Stream next0 s0) = let
--   unfold s = case next0 s of
--     Done       -> []
--     Skip s'    -> unfold s'
--     Yield x s' -> x : unfold s'
--   in unfold s0
-- * Thus 'stream' is a syntactic translation of [] and (:)
-- * 'unstream' is an unfoldr of non-recursive [a] augmented with Skip

-- Tree a b = Leaf a | Fork b (Tree a b) (Tree a b)
-- TreeStream a b = ∃s. Stream (s -> Step a b s) s
-- TreeStep a b s = Leaf a | Fork b s s | Skip s

-- * second order Catas must fuse with cata-build
-- * indexing functions? = buildl | buildr

data RecFn
 = Cata    Term -- term successfully rewritten as a (higher-order) Cata
 | Stream  Term -- ie. unstream < f < stream
 | Unboxed Term -- no data
 | Weird   Term -- mixes second-order cata and stream

--data ArgKind
--  = APrim PrimType
--  | AFunction [ArgKind] ArgKind
--  | ARecord   (IntMap ArgKind)
--  | ASum      (IntMap SumRep)
--  | APoly
--  | ARec -- only in Array or Tree (also fn return | any covariant position?)
--data SumRep = Enum | Peano | Wrap | Array [ArgKind] | Tree [ArgKind]

type SimplifierEnv s = StateT (Simplifier s) (ST s)
data Simplifier s = Simplifier {
   _thisMod     :: IName
 , _extBinds    :: V.Vector (V.Vector Expr)
 , _cBinds      :: MV.MVector s Bind
 , _nApps       :: Int
 , _argTable    :: MV.MVector s Term -- used for eta reduction `(ArgKind , Term)` ?
 , _betaStack   :: BitSet -- list of fn binds being beta-reduced (check for stacked reductions of same fn)
 , _self        :: Int -- the bind we're simplifying (is probably recursive)

 , _caseArgs    :: BitSet
 , _caseFnArgs  :: BitSet

 , _caseCount   :: Int -- unique i for every case in the function
 , _streamCases :: [Term]
 , _streamOK    :: Bool -- indicate if suitable for stream transformation
 , _recLabels   :: IM.IntMap (V.Vector Int)
}; makeLenses ''Simplifier
