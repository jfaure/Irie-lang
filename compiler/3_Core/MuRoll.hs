module MuRoll where
import CoreSyn
import ShowCore()
import CoreUtils
import Data.Functor.Foldable
import Data.List
import qualified Data.List.NonEmpty as NE

indexed :: Traversable f => f a -> (f (Int , a) , Int)
indexed f = traverse (\t -> get >>= \i -> modify (1+) $> (i , t)) f `runState` 0

---------------------
-- tighten μ-types --
---------------------
-- μ-roll cata checks only the 1 enclosing layer at each type constructor
-- There exists a few tricky cases:
-- | merge types as they are rolled: ⊤ & A
-- foldr1 : ∏ A B → (A → A → A) → µb.[Cons {A , µb.[Cons {⊤ , ⊤} | Nil]}] → A
--       => ∏ A B → (A → A → A) → µb.[Cons {A , b} | Nil] → A
-- | merge equivalent μ-variables (a,b) while rolling 2 branches; This requires a retraversal to rename μ-bound
-- rec1 v = { a = rec1 v , b = rec1 v }
--     ∏ A B → ⊤ → {a : µa.{a : a , b : µb.{a : a , b : b}} , b : µb.{a : µa.{a : a , b : b} , b : b}}
--  => ∏ A B → ⊤ → µa.{a : a , b : a}
-- | interleaved μs
-- flattenTree : ∏ A B C D → µb.[Node {A , µc.[Nil | Cons {b , c}]}] → µd.[Nil | Cons {A , d}]
-- This may need to know the polarity, for top/bot and to rm negative recursion
type Roller = [THead (Maybe Type)] -- x to μx. binder [TypeF] typeconstructor wrappers
data TypeRoll
 = NoRoll    { forgetRoll' :: Type }
 | BuildRoll { forgetRoll' :: Type , mus :: NonEmpty (Int , Roller , Type) } -- μVar + tycon wrappers + bounds per mu
 | Rolling   { forgetRoll' :: Type , muR :: Int , roller :: Roller , resetRoll :: Roller }
 deriving Show
forgetRoll x = {-d_ (rollTy x)-} (forgetRoll' x)

-- 1. merge sub-builds
-- 2. attempt to merge
mergeRolls (NoRoll t) b = case b of
  NoRoll t2        -> NoRoll (mergeTypes True t t2) -- TODO pos/neg type merge?!
  BuildRoll a ms   -> BuildRoll (a {-mergeTypes True a t-}) ms
  Rolling a m r z  -> Rolling   (a {-mergeTypes True a t-}) m r z
mergeRolls a b@NoRoll{} = mergeRolls b a
mergeRolls (BuildRoll a ms) (BuildRoll a2 ms2) = BuildRoll (mergeTypes True a a2) (ms <> ms2)
mergeRolls (Rolling a m r z) (Rolling a2 m2 _r2 _z2) = case compare m m2 of
  EQ -> Rolling (mergeTypes True a a2) m r z
  LT -> cata rollType (patchMu m2 m $ mergeTypes True a a2)
  GT -> cata rollType (patchMu m m2 $ mergeTypes True a2 a)
mergeRolls a@BuildRoll{} b@Rolling{} = mergeRolls b a
mergeRolls (Rolling noopRoll m r _z) (BuildRoll noopBuild builds) = let
  -- * Attempt to continue the roll, if that fails fallback to the alternative build option
  -- tbounds = NE.filter (\(n,_,_) -> n == m) builds <&> (\(_,_,b) -> b)
  -- builds & \((bm , br , bty) :| []) -> on (==) (fmap voidMus) br r

  clearMus :: Roller -> Roller -- Roller = [THead (Maybe Type)]
  clearMus = fmap $ fmap \case
    Just (TyGround [THMuBound _]) -> Nothing
    x -> x
  r' = clearMus r
  builds' = (\(_,r,_) -> clearMus r) <$> builds
  patchMu = mapTHeads \case
    THMuBound i | i == m -> THMuBound (NE.head builds & \(n,_,_) -> n)
    x -> x
  -- TODO v need to also set Just (TyGround [THMuBound _]) to Nothing to continue rolling!
--patchRoller = fmap $ fmap (\case { Just (TyGround [THMuBound _]) -> Nothing ; x->x})
  in (if any (r' ==) builds'
--   then Rolling noopRoll m r z
     then BuildRoll (cata (embed . patchMu) noopBuild) (builds) --((\(m,r,t) -> (m , patchRoller r , t)) <$> builds)
     else BuildRoll (mergeTypeList True (noopRoll : noopBuild : [])) builds)
-- & trace @Text ("roll-build: " <> show m <> "\n" <> show r <> "\n" <> show builds <> "\n")

-- compute typeRolls from a single THead (each sub-branch of tycons).
-- if. μ-bound in hole start μ-build
-- if. Build in a hole => if μ-binder: switch build to roll ||| continue build
-- if. Roll in hole check if roll ok: roll and reset ||| test more layers
-- TODO use forget-roll properly, atm it mixes layers and is unreliable
rollTHead :: BitSet -> [Int] -> THead TypeRoll -> TypeRoll
rollTHead vs ms th = let
  addMu m t@(TyGround [THMu n _]) = if n == m then t else error "internal error stacked μ"
  addMu m t = TyGround [THMu m t]
  noop = let tt = [forgetRoll <$> th] in if vs == 0 then TyGround tt else TyVars vs tt
  (ith , nBranches) = indexed th :: (THead (Int , TypeRoll) , Int)
  layer :: Int -> THead (Maybe Type) -- void out rec-branch for (==)
  layer i = ith <&> \(j , t) -> if i == j then Nothing else Just (forgetRoll t)
  isArr = case ith of { THTyCon THArrow{} -> True ; _ -> False }
  negRec i = isArr && i /= nBranches - 1
  -- v depth 1 inspection of each branch
  mkRoll :: Int -> TypeRoll -> [TypeRoll]
  mkRoll i = \case -- traceShow (i ,  t) t of
    BuildRoll _ty mus -> [mergeRollsNE $ mus <&> \(m , rollFn , b) -> let l = layer i : rollFn in
      if m `elem` ms
      then let r = reverse l in Rolling (addMu m (mergeTypes True b noop)) m r r
      else BuildRoll noop ((m , l , b) :| [])]
    Rolling ty m (r : nextRolls) reset -> {-trace (prettyTyRaw ty <> " <=> " <> prettyTyRaw noop)-}
      -- TODO ? check subtype (roughly eq modulo μ and bounds)
      if negRec i || layer i /= r
      then [] -- No Roll
      else [Rolling ty m (nextRolls <|> reset) reset]
    NoRoll _ -> []
    x -> error $ show x
  in case concat (Prelude.imap mkRoll (toList th)) of
    [] -> case ms of
      []  -> NoRoll noop
      [m] -> BuildRoll (TyGround [THMuBound m]) ((m , [] , noop) :| []) -- merge mu-bounds upwards
      m:_ -> BuildRoll (TyGround [THMuBound m]) ((m , [] , noop) :| []) -- TODO hack (intmap.ii needs this though)
    x : xs -> foldr mergeRolls x xs

rollType :: TypeF TypeRoll -> TypeRoll
rollType this = let
  -- Compute typeroll from a type merge
  aggregateBranches :: BitSet -> ([Int] , [THead TypeRoll]) -> TypeRoll
  aggregateBranches vs subs = let mkTy vs t = if vs == 0 then TyGround t else TyVars vs t
    in case subs of
    ([], xs) -> case rollTHead vs [] <$> xs of
      [] -> NoRoll (mkTy vs (fmap forgetRoll <$> xs))
      xs -> mergeTRolls xs
    (m , []) -> let allEq l = and (zipWith (==) l (drop 1 l)) in case m of
      mh:_ | allEq m -> BuildRoll (mkTy vs [THMuBound mh]) ((mh , [] , (TyGround [])) :| [])
      _   -> error (show m)
    (ms , xs) -> mergeTRolls (rollTHead vs ms <$> xs)
  -- TODO There should never be more than 1 μ , μs would have been merged already
  partitionMus g = let (ms , gs) = Data.List.partition (\case {THMuBound{} -> True ; _ -> False}) g
    in (ms <&> (\(THMuBound m) -> m) , gs)
  in case this of
  TyVarsF vs g -> aggregateBranches vs (partitionMus g)
  TyGroundF g  -> aggregateBranches 0  (partitionMus g)
  _ -> NoRoll (embed $ forgetRoll <$> this)

mergeTRolls :: [TypeRoll] -> TypeRoll         = \case { x : xs -> foldr mergeRolls x xs ; [] -> _ }
mergeRollsNE :: NonEmpty TypeRoll -> TypeRoll = \(x :| xs) -> foldr mergeRolls x xs

-- substitute mu-bounds for another (merge recursive type vars once they are rolled into contact)
patchMu :: Int -> Int -> Type -> Type
patchMu n m = mapTHeads' \case { THMuBound x | x == n -> THMuBound m ; THMu x t | x == n -> THMu m t ; x -> x }

deriving instance Show (THead (Maybe Type))
deriving instance Show (TyCon TypeRoll)
deriving instance Show (TyCon (Maybe Type))
deriving instance Show (THead TypeRoll)
