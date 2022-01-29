-- Externs:
-- resolve things that were out of scope when parsed
-- * things in scope, but defined later
-- * primitives: (note. prim bindings are CoreSyn)
-- * imported modules
-- * extern functions (esp. C)
-- * imported label/field names should overwrite locals (they are supposed to be the same)
module Externs (GlobalResolver(..) , addModule2Resolver , primResolver , primBinds , Import(..) , Externs(..) , readParseExtern , readQParseExtern , readLabel , readField , readPrimExtern , resolveImports , typeOfLit)
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

data GlobalResolver = GlobalResolver {
   modCount      :: Int
 , modNameMap    :: M.Map HName IName -- module HName -> Iname
 , globalNameMap :: M.Map HName (IM.IntMap IName) -- HName -> ModuleIName -> IName
 , allBinds      :: V.Vector (V.Vector (HName , Expr))
 , labelHNames   :: V.Vector (V.Vector HName)
 , fieldHNames   :: V.Vector (V.Vector HName)
 , lnames        :: M.Map HName QName --V.Vector (V.Vector HName)
 , fnames        :: M.Map HName QName --V.Vector (V.Vector HName)

  -- HName -> (MFIName -> ModuleIName)
 , globalMixfixWords :: M.Map HName (IM.IntMap [QMFWord])
} deriving Show

-- clear a module from the global resolver; need to call whenever re-checking a module, in case bindings were removed
-- expensive
--rmModule :: ModuleIName -> V.Vector HName -> GlobalResolver -> GlobalResolver
--rmModule modNm names resolver = let voidOut mp = if IM.null mp then Nothing else Just mp
--  in resolver { globalNameMap
--  = V.foldl (\mp hNm -> M.update (voidOut . IM.filterWithKey (\k i -> k /= modNm)) hNm mp) (globalNameMap resolver) names }

-- default resolver used to initialise a cache
-- has no field/label names, so give an empty entry in its module slot
-- the 0 module ".compilerPrimitives" is the interface for cpu-instructions and other magic
primResolver :: GlobalResolver = GlobalResolver
  1 (M.singleton ".compilerPrimitives" 0) (IM.singleton 0 <$> primMap)
    (V.singleton primBinds) -- primitive bindings
    (V.singleton mempty) (V.singleton mempty) M.empty mempty mempty

-------------
-- Externs --
-------------
-- how to substite P.VExtern during mixfix resolution
data Externs = Externs {
   extNames     :: V.Vector ExternVar
 , extBinds     :: V.Vector (V.Vector (HName , Expr))   -- all loaded bindings
 , importLabels :: V.Vector QName
 , importFields :: V.Vector QName
} deriving Show

readPrimExtern e i   = snd ((extBinds e V.! 0) V.! i)

readLabel , readField :: Externs -> IName -> QName
readLabel (Externs nms binds ils ifs) l = ils V.! l
readField (Externs nms binds ils ifs) f = ifs V.! f

-- exported functions to resolve ParseSyn.VExterns
readQParseExtern (Externs nms binds ils ifs) modNm iNm = if modNm == V.length binds
  then ForwardRef iNm -- ie. not actually an extern
  else Imported $ case snd ((binds V.! modNm) V.! iNm) of
    Core f t -> Core (Var $ VQBind $ mkQName modNm iNm) t
    PoisonExpr -> PoisonExpr
    x -> error $ show x

readParseExtern e@(Externs nms binds ils ifs) i = case nms V.! i of
  Importable modNm iNm -> readQParseExtern e modNm iNm
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
resolveImports :: GlobalResolver -> M.Map HName IName
  -> (M.Map HName IName , M.Map HName IName)
  -> M.Map HName [MFWord] -> M.Map HName IName -> Maybe OldCachedModule
  -> (GlobalResolver , Externs)
resolveImports (GlobalResolver n modNames curResolver prevBinds lh fh l f curMFWords)
  localNames (labelMap , fieldMap) mixfixHNames unknownNames maybeOld = let

  oldIName = oldModuleIName <$> maybeOld
  modIName = fromMaybe n oldIName

  resolver :: M.Map HName (IM.IntMap IName) -- HName -> Modules with that hname
  resolver = let
    localsAndLabels = localNames --localNames `M.union` ((M.size localNames +) <$> labelMap)
    -- temporarily mark field/label names (use 2 bits in the iname, the module name is crucial to track their origin)
    -- resolveName could use 3 maps, but would be slow since frequently entire maps would come back negative
    labels = IM.singleton modIName . (`setBit` labelBit) <$> labelMap
    fields = IM.singleton modIName . (`setBit` fieldBit) <$> fieldMap
    in M.unionsWith (IM.unionWith const) [((\iNm -> IM.singleton modIName iNm) <$> localsAndLabels) , curResolver , labels , fields]

  mfResolver = M.unionWith IM.union curMFWords $ M.unionsWith IM.union $
    zipWith (\modNm map -> IM.singleton modNm <$> map) [n..] [map (mfw2qmfw n) <$> mixfixHNames]
 
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

  in ( GlobalResolver n modNames resolver prevBinds lh fh l f mfResolver
     , Externs { extNames = names unknownNames
               , extBinds = prevBinds
               , importLabels = mkTable l labelMap
               , importFields = mkTable f fieldMap
               })

addModule2Resolver (GlobalResolver modCount modNames nameMaps binds lh fh l f mfResolver)
  modIName modName newBinds lHNames fHNames labelNames fieldNames labelExprs
  = let modNames' = M.insert modName modIName modNames
        binds' = binds `V.snoc` (newBinds)-- V.++ (V.zip lHNames labelExprs))
        l' = alignWith (\case { This new -> mkQName modIName new ; That old -> old ; These new old -> old }) labelNames l
        f' = alignWith (\case { This new -> mkQName modIName new ; That old -> old ; These new old -> old }) fieldNames f
    in GlobalResolver (modIName + 1) modNames' nameMaps binds' (lh `V.snoc` lHNames) (fh `V.snoc` fHNames) l' f' mfResolver

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
  , let tys2TyHead  (args , t) = mkTyArrow (mkExtTy <$> args) (mkExtTy t) in
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
  [ ("addOverflow" , (AddOverflow , mkTyArrow [[THExt i] , []] []))
--, ("unlink"      , (Unlink , mkTyArrow [[THExt str] , mkTHArrow [THExt c,THExt str] (THExt str)] [THExt str]))
--, ("link"        , (Link , mkTHArrow [THExt c] (THExt str)))
  , ("strtol"      , (StrToL , mkTHArrow [THExt str] (THExt i)))
  , ("mkTuple"     , (MkTuple , [THTyCon $ THTuple mempty]))
  , ("ifThenElse"  , (IfThenE , [THBi 1 $ mkTHArrow [THExt b, THBound 0, THBound 0] (THBound 0) ]))
  ]

primInstrs :: [(HName , (PrimInstr , ([IName] , IName)))] =
  [ ("Arrow" , (TyInstr Arrow  , ([set,set] , set)))
  , ("IntN"  , (TyInstr MkIntN , ([i] , set)))
  , ("primLen" , (Len , ([ia] , i)))
  , ("ptr2maybe" , (Ptr2Maybe , ([set] , set)))

  , ("puts"  , (Puts , ([str] , i)))
  , ("putNumber" , (PutNbr  , ([i] , i)))
  , ("putChar"   , (PutChar , ([c] , c)))
  , ("getcwd"    , (GetCWD  , ([] , str)))
  , ("opendir"   , (OpenDir , ([str] , dirp)))
  , ("readdir"   , (ReadDir , ([dirp] , dirent)))

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
--PolyInt{} -> THPrim (PrimInt 32)
  Int 0     -> THPrim (PrimInt 1)
  Int 1     -> THPrim (PrimInt 1)
  Int{}     -> THPrim (PrimInt 32)
--Int{}     -> THPrim (PrimInt 32)
  Char{}    -> THPrim (PrimInt 8) --THExt 3
  x -> error $ "don't know type of literal: " <> show x
