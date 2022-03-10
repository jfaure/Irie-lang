{-# Language TemplateHaskell #-}
module BetaEnv where
{-
import CoreSyn
import ShowCore()
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector as V
import Control.Lens

-- # β-reduction of higher order functions can have exponential amounts of sharing
-- ! Do not duplicate applications unless they represent different work
-- * delay beta-reducing a module to maximise sharing when we do

-- ## Runtime higher-order (or polymorphic) functions that dup an argument:
-- Linear strict functions must indicate if they erase any argument, otherwise proceed as normal;
-- dup-lam: fn args are superpositions (list of n args); its body is then implicitly duped n times (one for each superposition)
-- args can be dupPtrs and can be duped again within the fn body
-- dup-App:  duping app-nodes requires writing the result to global memory (the other dup-branches could be far away)
-- dup-dup: shiftL the dupEdges bitSet
-- strict fns will have to be run once for each superposed | duped arg in a higher-order function
-- lazy   fns (constructors) write their params to global memory as new Dup-nodes (thunks)
-- DupNodes = global stack of Data with dupEdges bitSet to resolve dupPtrs (since a node may have multiple dupPtrs)
-- Arg = SupList [DupPtr | Data] ; Data = Con | Label | Literal (statically known)

-- # Linearise
-- VLocal | VBind | VExtern => LiNames
-- LiSub = | VLocal | VBind | VExtern | Dup Int LiSub -- dup id (left or right or multiple)
--   | NewDup -- β-reduction spawns sub-dup nodes (Dup-Con , Dup-Lam , App-Sup , App-Strict-Sup-args , Specialise)
-- Dups along different Case-branches are independant

-- Simplification
-- Irreducible LiNames left as is (substituted with themselves)
-- Case-of-Label ; Case-of-Case ; general constant-folding
-- Specialisation: If have a specialised LiName for the arg shapes
--   then dup the specialisation and use that
--   else sub with a LiName pointing to a specialisation
-- If re-specialising: dup the specialisation and beta-reduce

-- ? add LinSubs into dupNodes and make dupNodes optionally contain only 1 branch
type BetaEnv s = StateT (Beta s) (ST s)
data Beta s = Beta {
--   _thisMod     :: IName
-- , _extBinds    :: V.Vector (V.Vector Expr)
-- , _cBinds      :: MV.MVector s Bind
   _linSubs  :: MV.MVector s Term -- β-reduction can spawn fresh names via dup-ctr or dup-sup
 , _linCount :: Int

 , _dupNodes :: MV.MVector s Term -- multiple LiNames may point to the same dup node
 , _dupEdges :: BitSet -- handles arbitrary arity dups: use popcnt to recover indices into dupNodes for each new name
 , _dupCount :: Int
}; makeLenses ''Beta

sub :: LiName -> Term -> BetaEnv s ()
sub l t = use linSubs >>= \subs -> MV.write subs l t

readDupPtr a = use dupNodes >>= \dn -> use dupEdges >>= \de -> MV.read dn (popCount (de .&. setNBits a))

-- mk new names both pointing to a dup-node. If dup-node already exists, re-use it and shift the dupEdges BitSet
dup2 :: Term -> BetaEnv s (Term , Term)
dup2 t = (dupCount <<%= (2+)) >>= \a -> use dupNodes >>= \dn -> MV.write dn t *> (dupEdges %= (`setBit` a))
  $> (DupPtr a , DupPtr (a + 1))

betaReduceTop :: Int -> Term -> Term
betaReduceTop liCount term = runST $ do
  lins <- MV.generate liCount Lin
  betaReduce term `evalStateT` Beta lins

betaReduce :: Term -> BetaEnv s Term
betaReduce t = case t of
  Lin i -> use linSubs >>= (`MV.read` i)
--Dup a b term inTerm -> brDup a b term *> betaReduce inTerm
  App f args -> brApp f args

  -- Make sure to recurse into branches
  Cons fields -> _
  TTLens record lens op -> _
  Label l ars -> _
  Match ty branches d -> _
  Cast c a -> Cast c <$> betaReduce a

  -- non-recursive
  Lit{}    -> pure t
  Instr{}  -> pure t
  Poison{} -> pure t
  _ -> error $ show t

brApp :: Term -> [Term] -> BetaEnv s Term
brApp f args = case f of
  Abs ars free body ty -> zipWithM_ (\(i,_) t -> sub i t) ars args *> betaReduce body

  -- App-Sup: duplicate args and mk a Sup of 2 Apps
  Sup f g -> (dup `mapM` args) >>= \dups -> let (fArgs , gArgs) = unzip dups
    in betaReduce (Sup (App f $ Lin <$> fArgs) (App g $ Lin <$> gArgs))

  -- One-step term-rewriting
  -- Otherwise eliminate superpositions from the args and beta-reduce the superposition
  -- (+ {a0 a1} b)
  -- --------------------- App-Strict
  -- dup b0 b1 = b
  -- {(+ a0 b0) (+ a1 b1)}
  -- Instr | Match | Cast | TTLens
  f -> do
    apps <- elimSups f args -- A superposition of apps
    rewriteApp <$> apps     -- one-step simplification rules

elimSups f args = _

rewriteApp f args = case f of
--Match ty branches d | [scrut] <- args -> fuseMatch ty scrut branches d
  _ -> App f args

-- Dups involve subbing in things for LiNames
-- Dups are shallow operations spawn one constructor layer at a time (and reduce the top-level dups by one layer)
brDup :: LiName -> LiName -> Term -> BetaEnv s ()
brDup a b term = void $ case term of
  -- Dup-Label: dup all params & re-label the 2 lists
  Label l params -> (dup `mapM` params) >>= \dups -> let
    (p1 , p2) = unzip dups
    in sub a (Label l $ Lin <$> p1) *> sub b (Label l $ Lin <$> p2)

  Erase -> sub a Erase *> sub b Erase

  -- Dup-Lam: dup argNames and sub them with a superposition of the dups
  -- then Dup the body (requires reflection)
  Abs ars 0 body ty -> do
    args <- (dup . Lin . fst) `mapM` ars
--  free <- dup               `mapM` freeArgs
    zipWithM (\(i,_) (a1,a2) -> sub i (Sup (Lin a1) (Lin a2))) ars args
    (b1 , b2) <- dup body
    let (a1 , a2) = unzip args
        argTys = snd <$> ars
    sub a (Abs (zip a1 argTys) emptyBitSet (Lin b1) ty)
    sub b (Abs (zip a2 argTys) emptyBitSet (Lin b2) ty)

  Sup x y
   | True -> sub a x *> sub b y -- Dup-Sup-Lam (lambda body duplication)
   | otherwise -> do            -- Dup-Sup anything else
    (a1 , a2) <- dup x
    (b1 , b2) <- dup y
    sub a (Sup (Lin a1) (Lin a2)) *> sub b (Sup (Lin b1) (Lin b2))

  -- dup-copy: copy the literal
  t -> sub a t *> sub b t
  -}
