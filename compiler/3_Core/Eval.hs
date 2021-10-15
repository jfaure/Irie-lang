module Eval where
import Prim
import CoreSyn
import CoreUtils
import ShowCore()
import qualified Data.Vector.Mutable as MV
import qualified Data.IntMap as IM
import qualified Data.Vector as V

-- Always inline simple functions
-- Constant fold casts and up to scrutinees as much as possible (can have huge impact)
-- Const args valuable for function
-- eta reduction on lambdas

-- Case merge
-- exitification (float exit paths out of recursive functions)
-- liberate-case (unroll recursive fns once to avoid repeated case on free vars)
-- Pow app

-- Maths
-- * recognize series; esp sum and product

-- Deriving build-catas
-- * Ec = (∀α1..αn) ∀β -- constructor equation where B is the type parameter for recursion
-- 1. extract wrapper-worker functions, substitute wrapper freely in the worker
-- 2. worker has an outer case over an argument; attempt to fuse with the copy function
--  2.1 distrubute the id cata accross the case, then make a single cata
--  2.2 immediately make a cata, then fuse the outer cata (higher-order fusion);
-- * iff the recursive invocation needs an inherited attribute

-- 4 Cases
-- Stream -> Stream
-- fold   -> build
-- Stream -> Build  `foldl Cons` `zip`
-- fold   -> Stream `foldr Cons` (iff fold-build no fuse); inline builds and derive a stream

-- Fusion
-- * cata = same shape as recursive types: (nested recursion) (eg. fn a1 (recurse))
-- * simplify (cata - build) by replacing all constructors with the cata function
-- * Make stream (~unfoldr) versions for non cata functions
-- # Stream Build
--   if stream is required at some point (zip | foldl)
--   try to invert the foldr part of the stream
--   At worst have to reify a list (choose the smallest one) then stream it
-- # foldr Stream (also reverse = foldl (flip (:)) [])
--   Convert foldr to stream version. if foldr produces data, it can be fold-builded
-- # builder foldrs are streams and build-foldrs
-- # builder foldls are builds
-- # Streams writeable as foldr if the state has no accumulator (or reversible one like +)

-- foldr f s (build g) => g f s
-- stream (unstream s) => s
--
-- Try to rewrite function as a foldr (iff recurses in same way as a recursive data)
-- Fallback to (unstream . fn' . stream) iff left-fold and|or multiple list args
-- Stream a = ∃s. Stream (s → Step a s) s
-- Step a s =
--   | Done
--   | Skip  s
--   | Yield s a
--
-- Cannot fuse when the stream producer is not known;
-- but can push this dynamic choice inside the stream
--
-- Tree a b = Leaf a | Fork b (Tree a b) (Tree a b)
-- Stream a b = ∃s. Stream (s -> Step a b s) s
-- Step a b s = SLeaf a | SFork b s s | Skip s

conNothing : conJust : _ = [-1,-2..]

type2ArgKind :: Type -> ArgKind
type2ArgKind = _

type SimplifierEnv s = StateT (Simplifier s) (ST s)
data ArgKind
  = APrim PrimType
  | AFunction [ArgKind] ArgKind
  | ARecord   (IntMap ArgKind)
  | ASum      (IntMap SumRep)
  | APoly
  | ARec -- only in Array or Tree (also fn return | any covariant position?)
data SumRep = Enum | Peano | Wrap | Array [ArgKind] | Tree [ArgKind]

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

identifyLabels :: Type -> SimplifierEnv s ()
identifyLabels ty = let
  isMuBound = \case { THMuBound x -> True ; _ -> False}
  goL [THTyCon (THTuple t)] = (fst <$> V.filter (\(_,t) -> any isMuBound t) (V.imap (,) t))
  go = mapM_ goTH
  goTH = \case
    THBi b ty   -> go ty
    THMu x ty   -> go ty
    THTyCon s -> case s of
      THSumTy ls -> do
        let is = goL <$> ls
        modify $ \x->x{recLabels = IM.union (recLabels x) $ is}
      THTuple t   -> go `mapM_` t
      THProduct t -> go `mapM_` t
      THArrow t r -> (go `mapM_` t) *> go r
    x -> pure ()
  in go ty

simpleBind :: Int -> SimplifierEnv s Bind
simpleBind n = gets cBinds >>= \cb -> MV.read cb n >>= \b -> do
--traceM "\n"
  svN <- zeroNApps
  modify $ \x->x{self = n}
  MV.write cb n (BindOpt (0xFFFFFF) (Core (Var (VBind n)) [])) -- recursion guard
  new <- case b of
    BindOpt nApps body -> setNApps nApps *> pure body
    BindOK (Core t ty) -> (identifyLabels ty *> {-(gets recLabels) *>-} simpleTerm t) <&> \case
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
    gets recLabels <&> (IM.!? l) <&> \case
      Nothing -> Label l      ars
      Just  i -> RecLabel l i ars

  Match t branches d -> let
    -- add recLabel information
    go l (Core f t) = gets recLabels <&> (fromMaybe mempty . (IM.!? l)) >>= \is -> (\e' -> (is,Core e' t)) <$> simpleTerm f
    in IM.traverseWithKey go branches <&> \branches' -> RecMatch branches' d

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
