-- Optimiser: extremely aggressively attempt to bring eliminators next to introductions
module Eval where
import Prim
import CoreSyn
import CoreUtils
import ShowCore()
import qualified Data.Vector.Mutable as MV
import qualified Data.IntMap as IM
import qualified Data.Vector as V

-- * inline small functions & data functions
-- * constant fold tycons (casts/case/products) as much as possible (eg. case-of-case)
-- * static argument transformation => if args to a (local) fn are constant
--     make them free (might avoid dup node)
-- * push lambdas to avoid cloning `\b => (f b , f b)` = `(\b => f b , \b => f b)`
-- * Mutual datafns: need to inline one into the other to minimise data

-- # eliminate data fixpoints => Stream / Cata / Build
-- # isolate tycons and fuse with their eliminators
--   beta-reduce once all data args are available (successfully eliminated data)
--   give up on excessively transitive data (too many large function calls before case)

-- Deriving build-catas
-- * Ec = (∀α1..αn) ∀β -- constructor equation where B is the type parameter for recursion
-- 1. extract wrapper-worker functions, substitute wrapper freely in the worker
-- 2. worker has an outer case over an argument; attempt to fuse with the copy function
--  2.1 distrubute the id cata accross the case, then make a single cata
--  2.2 immediately make a cata, then fuse the outer cata (higher-order fusion);
-- * iff the recursive invocation needs an inherited attribute

-- Dynamic deforestation (multiple builds for right/left or both)
-- buildFn = (a->b->b) -> b -> b
-- List a = | Nil | Cons a (List a) | Build (R|L|B) buildFn buildFn
-- foldr k z (Build g) = g k z

-- Cases
-- stream (unStream s) = s
-- fold f z (build g)  = g f z (syntax translation (label -> Fn))
-- Stream Build     syntax translation (label -> label)
-- fold   unstream  (may as well do cata-build, and let the program stack recursive calls)
--
-- First order (no inherited attribute) Stream / Foldr can be used interchangeably
-- Commutative and Associative folds/stream can be reversed
-- fold f        -> Stream
-- Stream next z -> fold

-- Deriving plasma
-- * cata-build needs to handle all nil/cons identically, so (tail (last) or foldr1 (first))
-- * catas from fns with same shape as the recursive type
-- * when the stream producer unknown, push as a dynamic choice inside the stream
-- * ? Mixing of second order recursion direction (eg. randomly switching foldr and foldl)

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

-- # Plan
-- Derive a cata or a stream function
-- * attempt to fuse everything with stream fusion
-- * use cata-build only for second order cata
-- * indexing functions? = buildl | buildr

--type2ArgKind :: Type -> ArgKind
--type2ArgKind = _
--
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
   cBinds      :: MV.MVector s Bind
 , nApps       :: Int
-- , argTable :: MV.MVector s [(ArgKind , Term)] -- used for eta reduction
 , argTable    :: MV.MVector s [Term] -- used for eta reduction
 , self        :: Int -- the bind we're simplifying (is probably recursive)
 , caseCount   :: Int -- unique ident for every case in the function
 , streamCases :: [Term]
 , streamOK    :: Bool -- indicate if suitable for stream transformation
 , recLabels   :: IM.IntMap (V.Vector Int)
}

setNApps :: Int -> SimplifierEnv s ()
setNApps n = (modify $ \x->x{nApps = n})
zeroNApps :: SimplifierEnv s Int
zeroNApps= gets nApps <* (modify $ \x->x{nApps = 0})
incNApps :: SimplifierEnv s ()
incNApps = modify $ \x->x{nApps = 1 + nApps x}
getNewCaseNumber :: SimplifierEnv s Int
getNewCaseNumber = gets caseCount <* modify (\x->x{caseCount = caseCount x - 1})
addStreamCase :: Term -> SimplifierEnv s ()
addStreamCase c = modify $ \x->x{streamCases = c : streamCases x}

simplifyBindings :: Int -> Int -> MV.MVector s Bind -> ST s (Simplifier s)
simplifyBindings nArgs nBinds bindsV = do
  argEtas <- MV.replicate nArgs []
  execStateT (simpleBind `mapM` [0 .. nBinds-1]) Simplifier {
    cBinds      = bindsV
  , nApps       = 0 -- measure the size of the callgraph
  , argTable    = argEtas
  , self        = -1
  , caseCount   = -1 -- counts negative labels
  , streamCases = []
  , streamOK    = True
  , recLabels   = IM.empty
  }

simpleBind :: Int -> SimplifierEnv s Bind
simpleBind n = gets cBinds >>= \cb -> MV.read cb n >>= \b -> do
--traceM "\n"
  svN <- zeroNApps
  modify $ \x->x{self = n}
  MV.write cb n (BindOpt (0xFFFFFF) (Core (Var (VBind n)) tyBot)) -- recursion guard
  new <- case b of
    BindOpt nApps body -> setNApps nApps *> pure body
    BindOK isRec (Core t ty) -> simpleTerm t <&> \case
      -- catch top level partial application (ie. extra implicit args)
      App (Instr (MkPAp n)) (f2 : args2) -> let
        (arTs , retT) = getArrowArgs ty
        diff = n - length args2
        in Core (PartialApp arTs f2 args2) retT
      newT -> Core newT ty
    x -> pure $ PoisonExpr
  napps <- gets nApps <* setNApps svN
  let b = BindOpt napps new
  MV.write cb n (BindOpt napps new)
  pure b

simpleTerm :: Term -> SimplifierEnv s Term
simpleTerm t = let
  foldAbs argDefs' free body ty args = let
    (argDefs , trailingArgs , etaReducable) = partitionThese (align argDefs' args)
    in gets argTable >>= \aT -> do
      etaReducable `forM` \((i,ty) , arg) -> MV.modify aT (arg:) i
      tRaw <- simpleTerm body
      let t = case trailingArgs of { [] -> body ; ars -> App body ars }
      etaReducable `forM` \((i,ty) , arg) -> MV.modify aT (drop 1) i -- TODO what if stacking insertions ?
      pure $ case argDefs of
        []      -> t
  in case t of
  Var v -> case v of
    VBind i -> simpleBind i <&> \case
      BindOpt napps (Core new t) -> if False && napps < 1
        then new else Var (VBind i) -- directly inline small callgraphs
    VArg  i -> gets argTable >>= \at -> MV.read at i <&> fromMaybe t . head
    x -> pure (Var x)

  Cast c a -> pure t

  Abs argDefs' free body ty -> simpleTerm body <&> \b -> Abs argDefs' free b ty

  App f args -> incNApps *> case f of
    Abs argDefs' free body ty -> foldAbs argDefs' free body ty args
    Instr i -> (simpleTerm `mapM` args) <&> \args -> simpleInstr i args
--  Match retT branches d | [arg] <- args -> _-- mkSvState retT branches d arg
    fn -> simpleTerm fn >>= \case
      Abs argDefs' free body ty -> foldAbs argDefs' free body ty args
      fn -> App fn <$> (simpleTerm `mapM` args)

  Label l a -> do
    ars <- a `forM` \(Core f t) -> (`Core` t) <$> simpleTerm f
    gets recLabels <&> (IM.!? qName2Key l) <&> \case
      Nothing -> Label l      ars
      Just  i -> RecLabel l i ars

--Match t branches d -> let
--  -- add recLabel information
--  go l (Core f t) = gets recLabels <&> (fromMaybe mempty . (IM.!? l)) >>= \is -> (\e' -> (is,Core e' t)) <$> simpleTerm f
--  in IM.traverseWithKey go branches <&> \branches' -> RecMatch branches' d

  _ -> pure t

{-
-- a Case on one of the arguments
mkSvState retT branches d arg = mdo
  newCase <- getNewCaseNumber
--addStreamCase c

  bs <- branches `forM` \b -> simpleTerm b >>= \(Abs ars is t ty) -> do
    -- pack all needed state
    this <- gets self
    vars <- gets caseState
    resetCaseState
    let new = case t of
          -- Match over labels is perfect for stream fusion
          -- If any of the args are a self recursive call, save a CASE0 in their place
          Label i ars  -> let
            case0 = Label (-1)
            in
            checkRec <$> ars
          App (Var (VBind i)) ars | i == this -> _

          -- Sv free vars into CASEN marker
          App (Match _retT subBranches d) [ars] -> _

--        App f ars ->

          -- Cannot stream this; foldl over a builder accumulator must switch to build-cata
          x         -> x
    use streamOK <&> \case
      True  -> new
      False -> Abs ars is t ty
  pure bs
-}

simpleInstr i args = case i of
  GMPInstr j -> simpleGMPInstr j args
  Zext | [Lit (Int i)]   <- args -> Lit (Fin 64 i)
       | [Lit (Fin n i)] <- args -> Lit (Fin 64 i)
  i -> App (Instr i) args

simpleGMPInstr :: NumInstrs -> [Term] -> Term
simpleGMPInstr i args = let
  mkCmpInstr pred args = App (Instr (NumInstr (PredInstr pred))) args
  in case i of
  IntInstr Add
    | [Cast (CastInstr (GMPZext n)) (Lit (Int i)) , rarg] <- args -> App (Instr (GMPOther AddUI)) [Lit (Fin 64 i) , rarg]
    | [larg , Cast (CastInstr (GMPZext n)) (Lit (Int i))] <- args -> App (Instr (GMPOther AddUI)) [Lit (Fin 64 i) , larg]
    | _ <- args -> App (Instr (GMPInstr i)) args
  IntInstr Sub
    | [Cast (CastInstr (GMPZext n)) (Lit (Int i)) , rarg] <- args -> App (Instr (GMPOther UISub)) [Lit (Fin 64 i) , rarg]
    | [larg , Cast (CastInstr (GMPZext n)) (Lit (Int i))] <- args -> App (Instr (GMPOther SubUI)) [larg , Lit (Fin 64 i)]
    | _ <- args -> App (Instr (GMPInstr i)) args
  IntInstr Mul
    -- ? MulUI
    | [Lit (Fin 64 i) , rarg] <- args -> App (Instr (GMPOther MulSI)) args
    | [larg , Lit (Fin 64 i)] <- args -> App (Instr (GMPOther MulSI)) [Lit (Fin 64 i) , larg]
  PredInstr LECmp -- TODO other cmp types
    -- CMPAbsD CMPAbsUI
    -- TODO spawn the icmp instruction here
    | [Cast (CastInstr (GMPZext n)) (Lit (Int i)) , rarg] <- args ->
        mkCmpInstr GECmp [App (Instr (GMPOther CMPUI)) [rarg , Lit (Fin 64 i)] , Lit (Fin 32 0)] -- flip the icmp
    | [larg , Cast (CastInstr (GMPZext n)) (Lit (Int i))] <- args ->
        mkCmpInstr LECmp [App (Instr (GMPOther CMPUI)) [larg , Lit (Fin 64 i)] , Lit (Fin 32 0)]
  IntInstr IPow
    -- powmui ?
    | [Lit (Fin 64 _) , Lit (Fin 64 _)] <- args -> App (Instr (GMPOther UIPowUI)) args
    | [larg , Lit (Fin 64 _)]           <- args -> App (Instr (GMPOther PowUI)) args
  -- nothing to fold
  i -> App (Instr (GMPInstr i)) args
