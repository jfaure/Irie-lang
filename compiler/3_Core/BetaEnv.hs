-- # β-reduction of higher order functions can have exponential amounts of sharing
-- To share computations inside lambdas (partial applications); ! Do not gratuitously duplicate applications
{-# Language TemplateHaskell #-}
module BetaEnv where
import CoreSyn
import ShowCore()
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector as V
import Control.Lens

-- # Linearise CoreSyn => App Module (Bindings <> Externs)
-- Convert all Bindings to Args (LiNames): VLocal | VBind | VExtern => LiName
-- This gives lin info on all bindings and externs within the module and prepares the β-reduction

-- # β-Plan
-- 1. At PAp creation, papcreate returns a new simplified PAp
-- 2. Duped lambdas that end up sharing arguments must make PAps on the shared arg

-- * x + y + z has many possible paps to avoid sharing an addition...
-- ? | compile-fold (+ inline higher-order fn args) | interpret | fn entry-point table | sup-args | monomorphize (not scalable)

-- ~ Duped Labels = Stream; lazy fns duped incrementally; write their params to global memory as new Dup-nodes (thunks)
-- Since It's hard to tell how much of it will be needed by all dups nodes

-- * derivatives of Sups are also Sups; until dup at the end of dup-lam resolves them
-- * temp dups | sups inserted by reduction rules:
--   1. sub-dups constructor params (if lazy)
--   2. sup lambda arguments (implicitly duped lambda-body)
--   3. App-sub (sup fn) & Strict-App (sup args)
--   4. Dup-Sup-Main (dup each elem of superposition) & mk new superpositions
-- ? cloning Match lambdas (when pass through dup node)

-- Optimisations:
-- Desaturate CaseFn: case-splits not requiring all args should push extra args into each branch (so strict in first n args)
-- Case-of-Label ; Case-of-Case ; general constant-folding
-- Specialise li: 'dynamically' dup input binds: search for matching shapes in LiName specs
--   Just s  -> dup s (an App of duped Li)
--   Nothing -> dup li and make new specialisation
-- If re-specialising: dup the specialisation and beta-reduce
-- Don't erase bindings on last dup because we may spawn more specialisations

type BetaEnv s = StateT (Beta s) (ST s)
data Beta s = Beta {
--   _thisMod     :: IName
-- , _extBinds    :: V.Vector (V.Vector Expr)
-- , _cBinds      :: MV.MVector s Bind
   _linSubs  :: MV.MVector s Term -- dups and superpositions (Lin | Sup) varnames
 , _linCount :: Int
 , _dupEdges :: BitSet -- vv See below
}; makeLenses ''Beta

-- Dup-Edges:
-- 1 0 0 1 1 0
-- [A , B , C] => 1 C , 0 B , 2 A
-- 0's indicate uses of the substitution (none => Erase ; 1 => LiName ; 2+ => Dups)
-- Providing a new LiName pointing to existing node = 4 Bitwise operations on a BigInt:
insert0At de li     = (de `shiftR` li `shiftL` (li + 1)) .|. (de .&. (setNBits li))
liName2SubIdx de li = popCount (de .&. (setNBits (1 + li))) - 1
dupLi li = dupEdges %= (`insert0At` li)

getSubIdx li = use dupEdges <&> \de -> liName2SubIdx de li

setSub :: LiName -> Term -> BetaEnv s ()
setSub li t = getSubIdx li >>= \i -> use linSubs >>= \subs -> MV.write subs i t
getSub li   = getSubIdx li >>= \i -> use linSubs >>= \subs -> MV.read subs i

-- Spawn a new dup node for a Term
dupTerm t n = (linCount <<%= (n+)) >>= \li -> (dupEdges %= (`setBit` li)) *> setSub li t $> li

dup :: Term -> BetaEnv s (Term , Term)
dup t = case t of
  Lin li -> dupLi li $> (Lin li , Lin li)
  t      -> dupTerm t 2 <&> \li -> (Lin li , Lin (1 + li))

-- constant / predictable dup count ?
-- free dupnode on last read?
