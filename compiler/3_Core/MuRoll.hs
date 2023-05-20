module MuRoll where
import CoreSyn
import ShowCore()
import CoreUtils
import Data.Functor.Foldable
import Data.List
import qualified Data.List.NonEmpty as NE

fst3 (a,_,_) = a

indexed :: Traversable f => f a -> f (Int , a)
indexed f = traverse (\t -> get >>= \i -> modify (1+) $> (i , t)) f `evalState` 0

---------------------
-- tighten μ-types --
---------------------
-- There exists a few tricky cases:
-- | extract and merge μ-var co-occurences into outer binder
-- foldr1 : ∏ A B → (A → A → A) → µb.[Cons {A , µb.[Cons {⊤ , ⊤} | Nil]}] → A
--       => ∏ A B → (A → A → A) → µb.[Cons {A , b} | Nil] → A
-- | merge 2 equivalent μ-variables (a,b) while rolling 2 branches
-- rec1 v = { a = rec1 v , b = rec1 v }
--     ∏ A B → ⊤ → {a : µa.{a : a , b : µb.{a : a , b : b}} , b : µb.{a : µa.{a : a , b : b} , b : b}}
--  => ∏ A B → ⊤ → µa.{a : a , b : a}
-- | interleaved μs
-- flattenTree : ∏ A B C D → µb.[Node {A , µc.[Nil | Cons {b , c}]}] → µd.[Nil | Cons {A , d}]
-- This may need to know the polarity, for top/bot and to rm negative recursion
-- muBounds serves to propagate co-occurences of recursive vars upwards
type Roller = [THead (Maybe Type)] -- x to μx. binder [TypeF] typeconstructor wrappers
data TypeRoll
 = NoRoll    { forgetRoll' :: Type }
 | BuildRoll { forgetRoll' :: Type , mus :: NonEmpty (Int , Roller , Type) } -- μVar + tycon wrappers + bounds per mu
 | Rolling   { forgetRoll' :: Type , muR :: Int , roller :: Roller , resetRoll :: Roller }
 deriving Show
forgetRoll x = {-d_ (rollTy x)-} (forgetRoll' x)
-- forgetRoll but keeps μvar bounds
--dropRoll m = \case
--  BuildRoll uf ms -> mergeTypeList True $ uf : (filter (\(i,_,_) -> i `elem` m) (NE.toList ms) <&> \(_ , _ , t) -> t)
--  x -> forgetRoll x
--rollTy = \case
--  NoRoll{} -> "noroll"
--  BuildRoll{} -> "buildroll"
--  Rolling{} -> "rolling"

mergeTRolls :: [TypeRoll] -> TypeRoll
mergeTRolls = \case { x : xs -> foldr mergeRolls x xs ; [] -> _ }
mergeRollsNE :: NonEmpty TypeRoll -> TypeRoll
mergeRollsNE (x :| xs) = foldr mergeRolls x xs

-- substitute mu-bounds for another (merge recursive type vars)
patchMu :: Int -> Int -> Type -> Type
patchMu n m = let
  go = \case { THMuBound x | x == n -> THMuBound m ; THMu x t | x == n -> THMu m t ; x -> x }
  in cata $ \case
  TyGroundF g -> TyGround (go <$> g)
  TyVarsF v g -> TyVars v (go <$> g)
  x -> embed x

m_ = flip const-- d_
mergeRolls a b = -- d_ (rollTy a , rollTy b)
  (mergeRolls' a b)
mergeRolls' (NoRoll t) (NoRoll t2)       = NoRoll (mergeTypes True t t2) -- TODO pos/neg type merge?!
mergeRolls' (NoRoll _t) (BuildRoll a ms)  = BuildRoll (a {-mergeTypes True a t-}) ms
mergeRolls' (NoRoll _t) (Rolling a m r z) = Rolling   (a {-mergeTypes True a t-}) m r z
mergeRolls' a b@NoRoll{} = mergeRolls b a
mergeRolls' (Rolling a m r z) (Rolling a2 m2 _r2 _z2)
 | m == m2 = m_ ("roll-roll") $ Rolling (mergeTypes True a a2) m r z
 | m < m2  = m_ ("roll-roll" , m , m2) $ cata rollType (patchMu m2 m $ mergeTypes True a a2)
 | m > m2  = m_ ("roll-roll" , m , m2) $ cata rollType (patchMu m m2 $ mergeTypes True a2 a)

mergeRolls' (BuildRoll a ms) (BuildRoll a2 ms2) = m_ ("build-build" , fst3 <$> ms , fst3 <$> ms2) $
  BuildRoll (mergeTypes True a a2) (ms <> ms2)

mergeRolls' a@BuildRoll{} b@Rolling{} = mergeRolls b a
mergeRolls' (Rolling a m _r _z) (BuildRoll a2 ms)
 = m_ ("roll-build" , m , ms) $ let
   tbounds = NE.filter (\(n,_,_) -> n == m) ms <&> (\(_,_,b) -> b)
   in BuildRoll (mergeTypeList True (a : a2 : tbounds)) ms -- TODO merged roll + build somehow

rollType :: TypeF TypeRoll -> TypeRoll
rollType this = let
  -- ! we may be building | rolling μs out of multiple branches
  -- compute typeRolls from a single THead (each sub-branch of tycons).
  getTHeadTypeRoll :: Integer -> [Int] -> THead TypeRoll -> TypeRoll
  getTHeadTypeRoll vs ms th = let
    addMu m t@(TyGround [THMu n _]) = if n == m then t else error "internal error stacked μ"
    addMu m t = TyGround [THMu m t]
    this = let tt = [forgetRoll <$> th] in if vs == 0 then TyGround tt else TyVars vs tt
    ith = indexed th
    -- if. μ-bound in hole start μ-build
    -- if. Build in a hole => if μ-binder: switch build to roll ||| continue build
    -- if. Roll in hole check if roll ok: roll and reset ||| test more layers
    layer i = ith <&> \(j , t) -> if i == j then Nothing else Just (forgetRoll t) -- void out rec-branch for (==)
    -- TODO don't insert 'this' into rolls !! need to re-construct type at top to propagate μ-bounds
    -- 'this' is the current type, mkRoll examines each branch (one layer down)
    mkRoll :: Int -> TypeRoll -> [TypeRoll]
    mkRoll i = \case
      BuildRoll _ty mus -> [mergeRollsNE $ mus <&> \(m , rollFn , b) -> let l = layer i : rollFn
        in if m `elem` ms then let r = reverse l in Rolling (addMu m (mergeTypes True b this)) m r r
           else BuildRoll this ((m , l , b) :| [])]
      Rolling ty m (r : nextRolls) reset -> {-trace (prettyTyRaw ty <> " <=> " <> prettyTyRaw this)-}
        if layer i /= r -- TODO check subtype (roughly eq modulo μ and bounds)
        then [] -- NoRoll this
--      then NoRoll $ mkTy $ ith <&> \(j , oldT) -> if i == j then trace (prettyTyRaw ty) ty else forgetRoll oldT -- re-insert μ-bounds
        else [Rolling ty m (nextRolls <|> reset) reset]
      NoRoll _ -> []
      x -> error $ show x
    -- TODO use forget-roll properly, atm it mixes layers and is unreliable
    in case concat (Prelude.imap mkRoll (toList th)) of
      [] -> case ms of
        []  -> NoRoll this
        [m] -> BuildRoll (TyGround [THMuBound m]) ((m , [] , this) :| []) -- merge mu-bounds upwards
        _ -> _ -- merge μs build-build style
      x : xs -> foldr mergeRolls x xs

  -- Compute typeroll from a type merge
  aggregateBranches :: BitSet -> ([Int] , [THead TypeRoll]) -> TypeRoll
  aggregateBranches vs subs = let mkTy vs t = if vs == 0 then TyGround t else TyVars vs t
    in case subs of
    ([], xs) -> case getTHeadTypeRoll vs [] <$> xs of
      [] -> NoRoll (mkTy vs (fmap forgetRoll <$> xs))
      xs -> mergeTRolls xs
    (m , []) -> let allEq l = and (zipWith (==) l (drop 1 l)) in case m of
      mh:_ | allEq m -> BuildRoll (mkTy vs [THMuBound mh]) ((mh , [] , (TyGround [])) :| [])
      _   -> error (show m)
    (ms , xs) -> mergeTRolls (getTHeadTypeRoll vs ms <$> xs)
  partitionMus g = let (ms , gs) = Data.List.partition (\case {THMuBound{} -> True ; _ -> False}) g
    in (ms <&> (\(THMuBound m) -> m) , gs)
  in case this of
  TyVarsF vs g -> aggregateBranches vs (partitionMus g)
  TyGroundF g  -> aggregateBranches 0  (partitionMus g)
  _ -> NoRoll (embed $ forgetRoll <$> this)

deriving instance Show (THead (Maybe Type))
deriving instance Show (TyCon TypeRoll)
deriving instance Show (TyCon (Maybe Type))
deriving instance Show (THead TypeRoll)
