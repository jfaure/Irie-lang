-- Externs:
-- resolve things that were out of scope when parsed
-- * things in scope, but defined later
-- * primitives: (note. prim bindings are CoreSyn)
-- * imported modules
-- * extern functions (esp. C)
-- * imported label/field names should overwrite locals (they are supposed to be the same)
--
-- * The 0 module (compiler primitives) is used to mark tuple fields (forall n 0.n)
module Externs (GlobalResolver(..) , ModDeps, ModDependencies(..), addModule2Resolver , addModName , primResolver , primBinds , Import(..) , Externs(..) , readParseExtern , readQParseExtern , readLabel , readField , readPrimExtern , resolveImports , typeOfLit , addDependency)
where
import Builtins ( primBinds, primMap, typeOfLit )
import CoreSyn
import ShowCore()
import MixfixSyn ( mfw2qmfw, MFWord, QMFWord )
import qualified ParseSyntax as P ( NameMap )
import qualified BitSetMap as BSM ( singleton )
import qualified Data.IntMap as IM ( IntMap, filterWithKey, singleton, toList, union )
import qualified Data.Map.Strict as M ( Map, (!?), member, size, insert, singleton, traverseWithKey, unionWith, unionsWith, update )
import qualified Data.Vector.Mutable as MV ( length, unsafeGrow, unsafeNew, write )
import qualified Data.Vector as V ( Vector, (!), create, foldl, singleton, unsafeFreeze, unsafeThaw )

-----------------
-- Import Tree --
-----------------
-- Imports are typechecked binds + parsed nameMap
data Import = Import {
    importNames :: P.NameMap
  , importBinds :: V.Vector (HName , Bind)
}

-- only direct dependencies are saved; main tracks the work stack to detect cycles
type ModDeps = Integer -- bitmask
data ModDependencies = ModDependencies { deps :: Integer , dependents :: Integer } deriving Show

data GlobalResolver = GlobalResolver {
   modCount      :: Int
 , modNameMap    :: M.Map HName IName -- module HName -> Iname
 , globalNameMap :: M.Map HName (IM.IntMap IName) -- HName -> ModuleIName -> IName
 , lnames        :: M.Map HName QName -- TODO rm
 , fnames        :: M.Map HName QName
 , modNamesV     :: V.Vector HName
 , allBinds      :: V.Vector (V.Vector (HName , Expr))
 , labelHNames   :: V.Vector (V.Vector HName)
 , fieldHNames   :: V.Vector (V.Vector HName)
 , dependencies  :: V.Vector ModDependencies

  -- HName -> (MFIName -> ModuleIName)
 , globalMixfixWords :: M.Map HName (IM.IntMap [QMFWord])
} deriving Show

-- basic resolver used to initialise a cache
-- the private 0 module ".compilerPrimitives" contains:
--  * cpu-instructions binds
--  * tuple fields: 0.[0..]
--  * extra labels (esp. for demutualisation and other optimisations)
primResolver :: GlobalResolver = let primModName = "(builtinPrimitives)" in
  GlobalResolver
  1 (M.singleton primModName 0) (IM.singleton 0 <$> primMap)
  mempty mempty
  (V.singleton primModName)
  (V.singleton primBinds) -- primitive bindings
  (V.singleton mempty) (V.singleton mempty) (V.singleton (ModDependencies 0 0)) mempty

-------------
-- Externs --
-------------
-- how to substitute P.VExtern during mixfix resolution
data Externs = Externs {
   extNames      :: V.Vector ExternVar
 , extBinds      :: V.Vector (V.Vector (HName , Expr)) -- all loaded bindings (same as in global resolver)
 , importLabels  :: V.Vector QName
 , importFields  :: V.Vector QName
 , eModNamesV    :: V.Vector HName
} deriving Show

readPrimExtern e i   = snd ((extBinds e V.! 0) V.! i)

readLabel , readField :: Externs -> IName -> QName
readLabel exts l = if l < 0 then mkQName 0 (-1 - l) else exts.importLabels V.! l
readField exts f = if f < 0 then mkQName 0 (-1 - f) else exts.importFields V.! f

-- exported functions to resolve ParseSyn.VExterns
readQParseExtern :: BitSet -> Int -> Externs -> Int -> IName -> CoreSyn.ExternVar
readQParseExtern openMods thisModIName (exts :: Externs) modNm iNm = if
  | modNm == thisModIName    -> ForwardRef iNm -- ie. not actually an extern
  | openMods `testBit` modNm -> Imported $ case snd ((exts.extBinds V.! modNm) V.! iNm) of
    e@(Core f t) -> case f of -- inline trivial things
      Lit{}   -> e
      Instr{} -> e
      Var{}   -> e -- var indirection
      _ -> Core (Var $ VQBind $ mkQName modNm iNm) t
    PoisonExpr -> PoisonExpr
    x -> x -- types and sets
  | otherwise -> NotOpened (exts.eModNamesV V.! modNm) (fst ((exts.extBinds V.! modNm) V.! iNm))

readParseExtern openMods thisModIName exts i = case exts.extNames V.! i of
  Importable modNm iNm -> readQParseExtern openMods thisModIName exts modNm iNm
  x -> x

-- First resolve names for a module, then that module can be added to the resolver
-- We need to resolve INames accross module boundaries.
-- Externs are a vector of CoreExprs, generated as: builtins ++ concat imports;
-- which is indexed by the permuation described in the extNames vector.
-- * primitives must always be present in GlobalResolver
resolveImports :: GlobalResolver -> IName -> M.Map HName IName
  -> (M.Map HName IName , M.Map HName IName)
  -> M.Map HName [MFWord] -> M.Map HName IName -> Maybe OldCachedModule
  -> (GlobalResolver , Externs)
resolveImports (GlobalResolver modCount modNames curResolver l f modNamesV prevBinds lh fh deps curMFWords)
  modIName localNames (labelMap , fieldMap) mixfixHNames unknownNames maybeOld = let

  oldIName = oldModuleIName <$> maybeOld

  resolver :: M.Map HName (IM.IntMap IName) -- HName -> Modules with that hname
  resolver = let
    -- temporarily mark field/label names (use 2 bits from the iname, not the module name which tracks their origin)
    -- instead resolveName could use 3 maps, but would be slow since frequently entire maps would come back negative
    labels = IM.singleton modIName . (`setBit` labelBit) <$> labelMap
    fields = IM.singleton modIName . (`setBit` fieldBit) <$> fieldMap
    -- Deleted names from the old module won't be overwritten so must be explicitly removed
    rmStaleNames nameMap = let
      collect = V.foldl (\stale nm -> if M.member nm localNames then stale else nm : stale) []
      staleNames = fromMaybe [] ((collect . oldBindNames) <$> maybeOld) :: [HName]
      in case oldIName of
        Just oldMod -> foldr (\staleName m -> M.update (Just . IM.filterWithKey (\k _v -> k /= oldMod)) staleName m) nameMap staleNames
        Nothing -> nameMap
    in rmStaleNames $ M.unionsWith IM.union
      [((\iNm -> IM.singleton modIName iNm) <$> localNames) , curResolver , labels , fields]

  mfResolver = M.unionWith IM.union curMFWords $ M.unionsWith IM.union $
    zipWith (\modNm map -> IM.singleton modNm <$> map) [modIName..] [map (mfw2qmfw modIName) <$> mixfixHNames]

  -- TODO filter modules in scope & remove fields !
  resolveName :: HName -> ExternVar -- (ModuleIName , IName)
  resolveName hNm = let
    binds   = IM.toList <$> (resolver   M.!? hNm)
    mfWords = IM.toList <$> (mfResolver M.!? hNm)
    flattenMFMap = concatMap snd
    in case (binds , mfWords) of
    (Just [] , _)  -> NotInScope hNm -- this name was deleted from (all) modules
    -- inline compiler primitives
    (Just [(0     , iNm)] , Nothing) -> Imported $ snd ((prevBinds V.! 0) V.! iNm)
    (Just [(modNm , iNm)] , Nothing)
--    label applications look like normal bindings `n = Nil`
      | True <- testBit iNm labelBit -> let q = mkQName modNm (clearBit iNm labelBit)
        in Imported (Core (Label q []) (TyGround [THTyCon $ THSumTy (BSM.singleton (qName2Key q) (TyGround [THTyCon $ THTuple mempty]))]))
      | True <- testBit iNm fieldBit -> NotInScope hNm
      | True -> Importable modNm iNm
    (b , Just mfWords)
      | Nothing      <- b -> MixfixyVar $ Mixfixy Nothing              (flattenMFMap mfWords)
      | Just [(m,i)] <- b -> MixfixyVar $ Mixfixy (Just (mkQName m i)) (flattenMFMap mfWords)
    (Nothing      , Nothing) -> NotInScope hNm
    (Just many , _)          -> AmbiguousBinding hNm many

  -- convert noScopeNames map to a vector (Map HName IName -> Vector HName)
  names :: Map HName Int -> V.Vector ExternVar
  names noScopeNames = V.create $ do
    v <- MV.unsafeNew (M.size noScopeNames)
    v <$ (\nm idx -> MV.write v idx $ resolveName nm) `M.traverseWithKey` noScopeNames

  -- labels may be imported from elsewhere, else they are new and assigned to this module
  mkTable map localMap = V.create $ do
    v <- MV.unsafeNew (M.size localMap)
    let getQName hNm localName = case map M.!? hNm of -- if field imported, use that QName
          Just q | modName q /= modIName -> q -- iff not from the module we're recompiling
          _ -> mkQName modIName localName     -- new field introduced in this (modIName) module
    v <$ (\hNm localName -> MV.write v localName (getQName hNm localName))
         `M.traverseWithKey` localMap

  in ( GlobalResolver modCount modNames resolver l f modNamesV prevBinds lh fh deps mfResolver
     , Externs { extNames = names unknownNames
               , extBinds = prevBinds
               , importLabels = mkTable l labelMap
               , importFields = mkTable f fieldMap
               , eModNamesV   = modNamesV
               })

-- Often we deal with incomplete vectors (with holes for modules in the pipeline eg. when processing dependencies)
-- Unfortunately writing/caching them to disk requires full initialisation (error "" would trigger when writing)
-- the trashValue serves as an obviously wrong 'uninitialised' element which should never be read eg. "(Uninitialized)"
updateVecIdx :: a -> V.Vector a -> Int -> a -> V.Vector a
updateVecIdx trashValue v' i new = runST $ do
  v <- V.unsafeThaw v'
  let l = MV.length v
  g <- if l > i then pure v else do
    g <- MV.unsafeGrow v i
    g <$ [l..l+i-1] `forM` \i -> MV.write g i trashValue -- initialise with recognizable trash to help debug bad reads
  MV.write g i new
  V.unsafeFreeze g

addModName modIName modHName g = g
  { modCount   = modCount g + 1
  , modNameMap = M.insert modHName modIName (modNameMap g)
  , modNamesV  = updateVecIdx "(Uninitialized)" (modNamesV g) modIName modHName
  }

addDependency _imported _moduleIName r = r
-- { dependencies = let
--   ModDependencies deps dependents = if V.length (dependencies r) > moduleIName
--     then dependencies r V.! moduleIName
--     else ModDependencies emptyBitSet emptyBitSet
--   in updateVecIdx (ModDependencies 0 0) (dependencies r) moduleIName (ModDependencies (deps `setBit` imported) dependents)
-- }

addModule2Resolver (GlobalResolver modCount modNames nameMaps l f modNamesV binds lh fh deps mfResolver)
  modIName newBinds lHNames fHNames labelNames fieldNames _modDeps
  = let binds'     = updateVecIdx (V.singleton ("(Uninitialized)" , PoisonExpr)) binds modIName newBinds
        lh'        = updateVecIdx (V.singleton "(Uninitialized)") lh    modIName lHNames
        fh'        = updateVecIdx (V.singleton "(Uninitialized)") fh    modIName fHNames
--      deps'      = updateVecIdx (ModDependencies 0 0) deps modIName modDeps
        l' = alignWith (\case { This new -> mkQName modIName new ; That old -> old ; These _new old -> old }) labelNames l
        f' = alignWith (\case { This new -> mkQName modIName new ; That old -> old ; These _new old -> old }) fieldNames f
    in GlobalResolver modCount modNames nameMaps l' f' modNamesV binds' lh' fh' deps mfResolver
