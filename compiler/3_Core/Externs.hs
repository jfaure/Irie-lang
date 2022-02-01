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
import Prim
import qualified ParseSyntax as P
import CoreSyn
import MixfixSyn
import CoreUtils
import ShowCore()

import qualified Data.Map.Strict as M
import qualified Data.IntMap as IM
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV

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
-- the 0 module ".compilerPrimitives" is the interface for cpu-instructions and other magic
-- tuple fields: 0.[0..]
-- extra labels (esp. for demutualisation and other optimisations)
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
   extNames     :: V.Vector ExternVar
 , extBinds     :: V.Vector (V.Vector (HName , Expr)) -- all loaded bindings (same as in global resolver)
 , importLabels :: V.Vector QName
 , importFields :: V.Vector QName
} deriving Show

readPrimExtern e i   = snd ((extBinds e V.! 0) V.! i)

patchName bit q = let (m,i) = (modName q , unQName q) in mkQName m (clearBit i bit)
readLabel , readField :: Externs -> IName -> QName
readLabel (Externs nms binds ils ifs) l = {-patchName labelBit $ -} if l < 0 then mkQName 0 (-1 - l) else ils V.! l
readField (Externs nms binds ils ifs) f = {-patchName labelBit $ -} if f < 0 then mkQName 0 (-1 - f) else ifs V.! f

-- exported functions to resolve ParseSyn.VExterns
readQParseExtern thisModIName (Externs nms binds ils ifs) modNm iNm = if modNm == thisModIName
  then ForwardRef iNm -- ie. not actually an extern
  else Imported $ case snd ((binds V.! modNm) V.! iNm) of
    Core f t -> Core (Var $ VQBind $ mkQName modNm iNm) t
    PoisonExpr -> PoisonExpr
    x -> error $ show x

readParseExtern thisModIName e@(Externs nms binds ils ifs) i = case nms V.! i of
  Importable modNm iNm -> readQParseExtern thisModIName e modNm iNm
  x -> x
--readParseExtern = \(Externs nms binds) i -> let (modNm , iNm) = nms V.! i
--  in if modNm >= V.length binds
--  then ForwardRef iNm
--  else Imported $ (binds V.! modNm) V.! iNm
--readMixfixExtern e (m,i) = (\(MFBind mfdef e) -> mfdef) $ (extBinds e V.! m) V.! i

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
--modIName = fromMaybe n oldIName

  resolver :: M.Map HName (IM.IntMap IName) -- HName -> Modules with that hname
  resolver = let
    -- temporarily mark field/label names (use 2 bits in the iname, need the module name to track their origin)
    -- instead resolveName could use 3 maps, but would be slow since frequently entire maps would come back negative
    labels = IM.singleton modIName . (`setBit` labelBit) <$> labelMap
    fields = IM.singleton modIName . (`setBit` fieldBit) <$> fieldMap
    in M.unionsWith IM.union [((\iNm -> IM.singleton modIName iNm) <$> localNames) , curResolver , labels , fields]

  mfResolver = M.unionWith IM.union curMFWords $ M.unionsWith IM.union $
    zipWith (\modNm map -> IM.singleton modNm <$> map) [modIName..] [map (mfw2qmfw modIName) <$> mixfixHNames]
 
  -- TODO filter modules in scope !
  -- TODO expand lambda-mixfixes with explicit holes
  -- TODO new Labels maybe already exist as imported labels!
  resolveName :: HName -> ExternVar -- (ModuleIName , IName)
  resolveName hNm = let
    binds   = IM.toList <$> (resolver   M.!? hNm)
    mfWords = IM.toList <$> (mfResolver M.!? hNm)
    flattenMFMap = concat . map snd
    in case (binds , mfWords) of
    (Just [] , _)  -> error $ "impossible: empty imap ?!"
    -- substitute compiler primitives directly
    (Just [(0     , iNm)] , Nothing) -> Imported $ snd ((prevBinds V.! 0) V.! iNm)
    (Just [(modNm , iNm)] , Nothing)
--    | True <- testBit iNm fieldBit -> Imported (Core (Field (mkQName modNm (clearBit iNm fieldBit)) []) [])
--    labels are weird in that they sometimes look like normal bindings `n = Nil`
      | True <- testBit iNm labelBit -> Imported (Core (Label (mkQName modNm (clearBit iNm labelBit)) []) [])
      | Just True <- ((==modNm) <$> oldIName) -> ForwardRef iNm -- discard old stuff
      | True -> Importable modNm iNm
    (b , Just mfWords)
      | Nothing      <- b -> MixfixyVar $ Mixfixy Nothing              (flattenMFMap mfWords)
      | Just [(m,i)] <- b -> MixfixyVar $ Mixfixy (Just (mkQName m i)) (flattenMFMap mfWords)
    (Nothing      , Nothing)         -> NotInScope hNm

    -- 2 names found: possibly we're recompiling a module which used to contain a duplicate name
    -- leaving deleted names in the resolver is likely far cheaper than eagerly cleaning all names on recompile
    -- perhaps make a hmap of oldbindnames?
    -- TODO what if deleted name becomes false positive?
    (Just [(am,ai) , (bm,bi)] , _) | Just old <- maybeOld ->
      let isOldName = hNm `elem` oldBindNames old in
      if      isOldName && am == oldModuleIName old then Importable bm bi
      else if isOldName && bm == oldModuleIName old then Importable am ai
      else AmbiguousBinding hNm
    (Just many , _)                 -> AmbiguousBinding hNm

  -- convert noScopeNames map to a vector (Map HName IName -> Vector HName)
  names :: Map HName Int -> V.Vector ExternVar
  names noScopeNames = V.create $ do
    v <- MV.unsafeNew (M.size noScopeNames)
    v <$ (\nm idx -> MV.write v idx $ resolveName nm) `M.traverseWithKey` noScopeNames

  -- labels may be imported from elsewhere, else they are new and assigned to this module
  mkTable map localMap = V.create $ do
    v <- MV.unsafeNew (M.size localMap)
    v <$ (\hNm localName -> MV.write v localName (fromMaybe (mkQName modIName localName) (map M.!? hNm)))
         `M.traverseWithKey` localMap

  in ( GlobalResolver modCount modNames resolver l f modNamesV prevBinds lh fh deps mfResolver
     , Externs { extNames = names unknownNames
               , extBinds = prevBinds
               , importLabels = mkTable l labelMap
               , importFields = mkTable f fieldMap
               })

-- Often we deal with incomplete vectors (with holes for modules in the pipeline (when processing dependencies))
-- Unfortunately writing/caching them to disk requires full initialisation (error "" would trigger before writing)
-- the trashValue serves as an obviously wrong 'uninitialised' element which should never be read
updateVecIdx :: a -> V.Vector a -> Int -> a -> V.Vector a
updateVecIdx trashValue v i new = runST $ do
  v <- V.unsafeThaw v
  let l = MV.length v
  g <- if l > i then pure v else do
    g <- MV.unsafeGrow v i
    g <$ [l..l+i-1] `forM` \i -> MV.write g i trashValue -- initialise with recognizable trash
  MV.write g i new
  V.unsafeFreeze g

addModName modIName modHName g = g
  { modCount   = modCount g + 1
  , modNameMap = M.insert modHName modIName (modNameMap g)
  , modNamesV  = updateVecIdx "(Uninitialized)" (modNamesV g) modIName modHName
  }

addDependency imported moduleIName r = r
  { dependencies = V.modify (\v -> MV.modify v (\d->d{dependents = (dependents d) `setBit` imported}) moduleIName) (dependencies r) }

addModule2Resolver (GlobalResolver modCount modNames nameMaps l f modNamesV binds lh fh deps mfResolver)
  isRecompile modIName modHName newBinds lHNames fHNames labelNames fieldNames modDeps
  = let binds'     = updateVecIdx (V.singleton ("(Uninitialized)" , PoisonExpr)) binds modIName newBinds
        lh'        = updateVecIdx (V.singleton "(Uninitialized)") lh    modIName lHNames
        fh'        = updateVecIdx (V.singleton "(Uninitialized)") fh    modIName fHNames
        deps'      = updateVecIdx (ModDependencies 0 0) deps modIName modDeps
        l' = alignWith (\case { This new -> mkQName modIName new ; That old -> old ; These new old -> old }) labelNames l
        f' = alignWith (\case { This new -> mkQName modIName new ; That old -> old ; These new old -> old }) fieldNames f
    in GlobalResolver modCount modNames nameMaps l' f' modNamesV binds' lh' fh' deps mfResolver

mkExtTy x = [THExt x]

---------------------------
-- Primitives / Builtins --
---------------------------
-- Primitives are built as a standard importable module
-- * construct a vector of primitives
-- * supply a (Map HName IName) to resolve names to indexes
getPrimIdx = (primMap M.!?)
getPrimTy nm = case getPrimIdx nm of -- case M.lookup nm primTyMap of
  Nothing -> panic $ "panic: badly setup primtables; " <> nm <> " not in scope"
  Just i  -> i

primMap = M.fromList $ zipWith (\(nm,_val) i -> (nm,i)) primTable [0..]
--primBinds :: V.Vector Expr = V.fromList $ snd <$> primTable
primBinds :: V.Vector (HName , Expr) = V.fromList primTable

primTable = concat
  [ (\(nm , x)         -> (nm , Ty [THPrim x]) )                  <$> primTys
  , let tys2TyHead  (args , t) = [mkTyArrow (mkExtTy <$> args) (mkExtTy t)] in
    (\(nm , (i , tys)) -> (nm , Core (Instr i) (tys2TyHead tys))) <$> primInstrs
  , (\(nm , (i , t))   -> (nm , Core (Instr i) t))                <$> instrs
  , (\(nm , e)         -> (nm , Ty [e]))                          <$> tyFns
-- , uncurry ExtFn <$> extFnBinds
  ]

primTys :: [(HName , PrimType)] =
  [ ("Bool"    , PrimInt 1)
  , ("Int"     , PrimInt 32)
  , ("Int64"   , PrimInt 64)
  , ("BigInt"  , PrimBigInt)
  , ("Char"    , PrimInt 8)
  , ("Nat"     , PrimNat 32)
  , ("Float"   , PrimFloat FloatTy )
  , ("Double"  , PrimFloat DoubleTy)
  , ("CharPtr" , PtrTo $ PrimInt 8 )
  , ("CString" , PtrTo $ PrimInt 8 )
  , ("IntArray", PrimArr $ PrimInt 32)
  , ("DIR*"    , POSIXTy DirP)
  , ("dirent*" , POSIXTy DirentP)
  ]

[i, bi, b, f, c, ia, str, set , i64 , dirp , dirent] = getPrimTy <$> ["Int", "BigInt" , "Bool", "Double", "Char", "IntArray", "CString", "Set" , "Int64" , "DIR*" , "dirent*"]

--substPrimTy i = THPrim $ primTyBinds V.! i

-- instrs are typed with indexes into the primty map
tyFns = [
--[ ("IntN" , (THPi [(0,(mkExtTy i))] [THInstr MkIntN [0]] M.empty))
--  ("->", (THPi [(0,[THSet 0]),(1,[THSet 0])] [THInstr ArrowTy [0, 1]] M.empty))
    ("Set" , THSet 0)
--  , ("_→_", (ArrowTy , ([set] , set)))
  ]

instrs :: [(HName , (PrimInstr , Type))] =
  [ ("addOverflow" , (AddOverflow , [mkTyArrow [[THExt i] , []] []]))
--, ("unlink"      , (Unlink , mkTyArrow [[THExt str] , mkTHArrow [THExt c,THExt str] (THExt str)] [THExt str]))
--, ("link"        , (Link , mkTHArrow [THExt c] (THExt str)))
  , ("strtol"      , (StrToL  , [mkTHArrow [THExt str] (THExt i)]))
  , ("mkTuple"     , (MkTuple , [THTyCon $ THTuple mempty]))
  , ("ifThenElse"  , (IfThenE , [THBi 1 [mkTHArrow [THExt b, THBound 0, THBound 0] (THBound 0) ]]))
  , ("getcwd"      , (GetCWD  , [THExt str]))

  -- TODO fix type (set -> set -> A -> B)
  , ("ptr2maybe"   , (Ptr2Maybe , [THBi 2 [mkTHArrow [THExt set , THExt set , THBound 0] (THBound 0)] ]))

   -- (Seed -> (Bool , A , Seed)) -> Seed -> %ptr(A)
  , ("unfoldArray"   , (UnFoldArr , let unfoldRet = mkTHArrow [THBound 0] (mkTHTuple [[THExt b] , [THExt c] , [THBound 0]])
      in [THBi 1 $ [mkTHArrow [THBound 0 , unfoldRet , THBound 0] (THExt str)]]))

  -- %ptr(A) -> (Bool , A , %ptr(A))    == str -> (Bool , char , str)
  , ("nextElem" , (NextElem , [mkTHArrow [THExt str] (mkTHTuple $ [[THExt b] , [THExt c] , [THExt str]])] ))

  , ("readFile"  , (ReadFile  , [mkTHArrow [THExt str] (THExt str)]))
  , ("writeFile" , (WriteFile , [mkTHArrow [THExt str] (THExt str)]))
  ]

primInstrs :: [(HName , (PrimInstr , ([IName] , IName)))] =
  [ ("Arrow" , (TyInstr Arrow  , ([set,set] , set)))
  , ("IntN"  , (TyInstr MkIntN , ([i] , set)))
  , ("primLen" , (Len , ([ia] , i)))

  , ("puts"  , (Puts , ([str] , i)))
  , ("putNumber" , (PutNbr  , ([i] , i)))
  , ("putChar"   , (PutChar , ([c] , c)))
  , ("opendir"   , (OpenDir , ([str] , dirp)))
  , ("readdir"   , (ReadDir , ([dirp] , dirent)))
  , ("direntName", (DirentName , ([dirent] , str)))

  , ("add64" , (NumInstr (IntInstr Add    ) , ([i64, i64] , i64) ))
  , ("add"   , (NumInstr (IntInstr Add    ) , ([i, i] , i) ))
  , ("sub"   , (NumInstr (IntInstr Sub    ) , ([i, i] , i) ))
  , ("pow"   , (NumInstr (IntInstr IPow   ) , ([i, i] , i) ))
  , ("mul"   , (NumInstr (IntInstr Mul    ) , ([i, i] , i) ))
  , ("div"   , (NumInstr (NatInstr UDiv   ) , ([i, i] , i) ))
  , ("rem"   , (NumInstr (NatInstr URem   ) , ([i, i] , i) ))
  , ("fdiv"  , (NumInstr (FracInstr FDiv  ) , ([f, f] , f) ))
  , ("frem"  , (NumInstr (FracInstr FRem  ) , ([i, i] , i) ))
  , ("fadd"  , (NumInstr (FracInstr FAdd  ) , ([f, f] , f) ))
  , ("fsub"  , (NumInstr (FracInstr FSub  ) , ([f, f] , f) ))
  , ("fmul"  , (NumInstr (FracInstr FMul  ) , ([f, f] , f) ))
--, ("fcmp"  , (NumInstr (FracInstr FCmp  ) , ([f, f] , f) ))
  , ("le"    , (NumInstr (PredInstr LECmp ) , ([i, i] , b) ))
  , ("ge"    , (NumInstr (PredInstr GECmp ) , ([i, i] , b) ))
  , ("lt"    , (NumInstr (PredInstr LTCmp ) , ([i, i] , b) ))
  , ("gt"    , (NumInstr (PredInstr GTCmp ) , ([i, i] , b) ))
  , ("eq"    , (NumInstr (PredInstr EQCmp ) , ([i, i] , b) ))
  , ("ne"    , (NumInstr (PredInstr NEQCmp) , ([i, i] , b) ))
  , ("zext"  , (Zext  , ([b] , i) ))
  , ("sdiv"  , (NumInstr (IntInstr SDiv) , ([i, i] , i) ))
  , ("srem"  , (NumInstr (IntInstr SRem) , ([i, i] , i) ))
  , ("bitXOR", (NumInstr (BitInstr Xor ) , ([i, i] , i) ))
  , ("bitAND", (NumInstr (BitInstr And ) , ([i, i] , i) ))
  , ("bitOR" , (NumInstr (BitInstr Or  ) , ([i, i] , i) ))
  , ("bitNOT", (NumInstr (BitInstr Not ) , ([i, i] , i) ))
  , ("bitSHL", (NumInstr (BitInstr ShL ) , ([i, i] , i) ))
  , ("bitSHR", (NumInstr (BitInstr ShR ) , ([i, i] , i) ))

  , ("gmp-putNumber" , (GMPPutNbr , ([bi] , i)))
  , ("gmp-add"  , (GMPInstr (IntInstr Add) , ([bi, bi] , bi) ))
  , ("gmp-sub"  , (GMPInstr (IntInstr Sub) , ([bi, bi] , bi) ))
  , ("gmp-mul"  , (GMPInstr (IntInstr Mul) , ([bi, bi] , bi) ))
  , ("gmp-le"   , (GMPInstr (PredInstr LECmp) , ([bi, bi] , b) ))
  ]

typeOfLit = \case
  String{}  -> THPrim $ PtrTo (PrimInt 8) --"CharPtr"
  Array{}   -> THPrim $ PtrTo (PrimInt 8) --"CharPtr"
  PolyInt{} -> THPrim PrimBigInt
  Int 0     -> THPrim (PrimInt 1)
  Int 1     -> THPrim (PrimInt 1)
  Int{}     -> THPrim (PrimInt 32)
  Char{}    -> THPrim (PrimInt 8) --THExt 3
  x -> error $ "don't know type of literal: " <> show x
