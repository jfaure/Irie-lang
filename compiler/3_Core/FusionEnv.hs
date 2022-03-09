{-# Language TemplateHaskell #-}
module FusionEnv where
import CoreSyn
import ShowCore()
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector as V
import qualified Data.Map as M
import Control.Lens

-- # β-reduction
-- ! Do not duplicate applications unless they represent different work
-- * duplicate Abs without duplicating body
-- * U → V may create redexes of type U or V
-- * amount of sharing can be so large it cannot be handled in elementary time in term size
--
-- Term |= S (inc all VBruijns found within / throw away the topmost argument)

-- Symmetric Interaction Calculus
-- a ~> b means a reduces to b
-- a <~ b means a is replaced by b
-- term
--   = λx. term      -- function
--   | (term term)   -- application
--   | x             -- variable
--   | x = term      -- definition
--   | term & term   -- superposition
-- Lambda application:
--   ((λx. body) arg) ~> body
--   x                <~ arg
-- Superposed application:
--   ((f0 & f1) x) ~> f0 K & f1 K
--                 <~ K = x
-- Lambda copy:
--   (v = λx. body) ~> v = body
--   v              <~ (λx0. v)
--   v              <~ (λx1. v)
--   x              <~ (x0 & x1)
-- Superposed copy:
--   (v = x0 & x1) ~>
--   v             <~ x0
--   v             <~ x1

-- # Fusion: extremely aggressively attempt to connect Matches to Labels
-- # Prep phase
-- eliminate data fixpoints => Stream / Cata / Build
-- Identify small functions which we intend to always inline
-- Identify CaseArgs CaseArgApp and CaseLensArgs => these require inlining into callsites

-- # Elimination phase
-- Proceed top-down pushing constants and constant labels inwards
-- eg. go z x@(Right ys) => if x is caseArg => inline go and fuse the case

-- Need to specialise; so recursive calls can bypass a Con > Match
-- case-of-label: constant fold
-- case-of-case : push outer case into each branch => many case-of-label
-- case-of-arg:
--   ConSpec => calls to F use a constant constructor on arg
-- case-of-(App arg _):
--   Want an arg that produces a constant label:
--     !Not all arguments to arg need to be constant for this to be fusable
--     Need to inline F into call-sites (partial specialisation | static arg)
--   Partial application (incl. freeVars):
--     | static arg => lift fnArg from recursive calls; so it can be binded to a non-Arg
--     | pap-spec   => conv fnArg to a PAp of a statically known function

-- # Other improvements
-- case-merge: extract sub-cases that scrutinize the same variable
-- case-liberate: unroll rec fns once to avoid repeated case on free-vars
-- Multi-if-folding: `case x - 10 of { 10 -> _ }` => `case x of { 20 -> _ }`

-- # Unboxed values
-- always-inline small functions
-- Lambda-of-Con: dup lambda to avoid duping args: (?!)
--   `\b => (f b , g b)` => `(\b0 => f b0 , \b1 => g b1)`
-- Mutuals: perhaps better as a double loop
-- Recognize series (sum/product)
-- Recognize neutral elements (0 for + , 1 for *)

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

-- # Specialisation: bypass `Match over Label` for constant structure passed to Abs
-- Specialisation: IntMap IBind SpecI
-- Order of operations

data RecFn
 = Cata    Term -- term successfully rewritten as a (higher-order) Cata
 | Stream  Term -- ie. unstream < f < stream
 | Unboxed Term -- no data
 | Weird   Term -- mixes second-order cata and stream

-- The big question: How much arg structure is needed for a specialisation to fuse something
data FuseArg -- Which args are case-split and how
 = NoBranch  -- Not case-split in this function (Presumably its built into the result and may be case-split later)
 | CaseArg   -- arg is case-split
 | CaseFnArg FuseArg -- arg is a fn whose result is case-split (upto given structure)

 | LensedArg {- Lens -} -- What structure of the arg must be known to fuse with a case

-- Re-use specialisations if the structure is identical
data ArgShape
 = ShapeNone
 | ShapeLabel ILabel [ArgShape]
 | ShapeQBind QName
 deriving (Eq , Ord , Show)

getArgShape = \case
  Label l params -> ShapeLabel l (getArgShape <$> params)
  Var (VQBind q) -> ShapeQBind q
  _ -> ShapeNone

type SimplifierEnv s = StateT (Simplifier s) (ST s)
data Simplifier s = Simplifier {
   _thisMod     :: IName
 , _extBinds    :: V.Vector (V.Vector Expr)
 , _cBinds      :: MV.MVector s Bind
 , _nApps       :: Int -- approximate complexity rating of a function
 , _argTable    :: MV.MVector s Term -- used for β reduction
 , _useArgTable :: Bool -- toggle for bypassing argTable (ie. if not simplifying the body of an App)
 , _bruijnArgs  :: V.Vector Term
 , _self        :: Int    -- the bind we're simplifying

 , _nSpecs      :: Int -- cursor for allocating new specialisations
 , _prevSpecs   :: Int -- specialisations already computed; new requests are: [prevSpecs .. nSpecs-1]
 , _tmpSpecs    :: MV.MVector s (Either QName IName , Int , [Term]) -- requested specialisations of q (bind) or i (spec)
 , _letSpecs    :: MV.MVector s (Maybe Term)  -- specialisations
 , _bindSpecs   :: MV.MVector s BitSet -- specialisation INames for each bind (to avoid respecialising things)
 , _cachedSpecs :: MV.MVector s (M.Map [ArgShape] IName) -- recover specialisations for same arg shapes
 -- recursive specialisations
 , _thisSpec    :: IName  -- wip spec
 , _recSpecs    :: BitSet -- specialisations that contain themselves (don't inline these)

  -- collect fns using specialisations not yet generated; will have to resimplify later
 , _hasSpecs    :: BitSet
 , _reSpecs     :: [IName] -- Bindings containing un-inlined specialisations

 , _specStack   :: BitSet -- Avoid recursive inline
 , _inlineStack :: BitSet -- Avoid recursive inline

 , _caseArgs    :: BitSet
 , _caseFnArgs  :: BitSet
}; makeLenses ''Simplifier

--data ArgKind
--  = APrim PrimType
--  | AFunction [ArgKind] ArgKind
--  | ARecord   (IntMap ArgKind)
--  | ASum      (IntMap SumRep)
--  | APoly
--  | ARec -- only in Array or Tree (also fn return | any covariant position?)
--data SumRep = Enum | Peano | Wrap | Array [ArgKind] | Tree [ArgKind]
