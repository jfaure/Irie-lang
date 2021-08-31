-- Externs:
-- resolve things that were out of scope when parsed
-- * things in scope, but defined later
-- * primitives: (note. prim bindings are CoreSyn)
-- * imported modules
-- * extern functions (esp. C)

module Externs (GlobalResolver(..) , addModule2Resolver , primResolver , primBinds , Import(..) , Externs(..)
  , readParseExtern , readQParseExtern , readPrimExtern , resolveImports , typeOfLit)
where
import Prim
import qualified ParseSyntax as P
import CoreSyn
import MixfixSyn
import CoreUtils
import ShowCore()

import qualified Data.Map as M
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
 , globalNameMap :: M.Map HName (IM.IntMap IName) -- HName -> IName -> ModuleIName
 , allBinds      :: V.Vector (V.Vector Expr)

  -- HName -> (MFIName -> ModuleIName)
 , globalMixfixWords :: M.Map HName (IM.IntMap [QMFWord])
} deriving Show

primResolver :: GlobalResolver = GlobalResolver 1 (IM.singleton 0 <$> primMap) (V.singleton primBinds) M.empty

-------------
-- Externs --
-------------
-- data Externsfor substituting P.VExtern during mixfix resolution
data Externs = Externs {
   extNames   :: V.Vector ExternVar
 , extBinds   :: V.Vector (V.Vector Expr)   -- all loaded bindings
} deriving Show

-- exported functions to resolve ParseSyn.VExterns
readQParseExtern = \(Externs nms binds) modNm iNm -> if modNm >= V.length binds
  then ForwardRef iNm -- ie. not available yet , must typecheck as forwardRef | mutual binding
  else Imported $ (binds V.! modNm) V.! iNm
readParseExtern  = \e@(Externs nms binds) i -> case nms V.! i of
  Importable modNm iNm -> readQParseExtern e modNm iNm
  x -> x

--readParseExtern = \(Externs nms binds) i -> let (modNm , iNm) = nms V.! i
--  in if modNm >= V.length binds
--  then ForwardRef iNm
--  else Imported $ (binds V.! modNm) V.! iNm
readPrimExtern e i   = (extBinds e V.! 0) V.! i
--readMixfixExtern e (m,i) = (\(MFBind mfdef e) -> mfdef) $ (extBinds e V.! m) V.! i

-- First resolve names for a module, then that module can be added to the resolver
-- We need to resolve INames accross module boundaries.
-- Externs are a vector of CoreExprs, generated as: builtins ++ concat imports;
-- which is indexed by the permuation described in the extNames vector.
-- * primitives must always be present in GlobalResolver
resolveImports :: GlobalResolver -> M.Map HName IName -> M.Map HName [MFWord] -> M.Map HName IName -> (GlobalResolver , Externs)
resolveImports (GlobalResolver n curResolver prevBinds curMFWords) localNames mixfixHNames unknownNames = let
--allBinds = prevAllBinds V.++ V.fromList (fmap (bind2Expr . snd) . importBinds <$> imports)
--allBinds = prevAllBinds `V.snoc` imported ---- V.++ V.fromList (fmap (bind2Expr . snd) . importBinds <$> imports)

  resolver :: M.Map HName (IM.IntMap IName) -- HName -> Modules with that hname
  resolver = M.unionWith IM.union curResolver $ M.unionsWith IM.union $
    zipWith (\modNm map -> (\iNm -> IM.singleton modNm iNm) <$> map) [n..] [localNames]

  mfResolver = M.unionWith IM.union curMFWords $ M.unionsWith IM.union $
    zipWith (\modNm map -> IM.singleton modNm <$> map) [n..] [map (mfw2qmfw n) <$> mixfixHNames]
 
  -- TODO filter modules in scope !
  -- TODO expand lambda-mixfixes with explicit holes
  resolveName :: HName -> ExternVar -- (ModuleIName , IName)
  resolveName hNm = let
    binds   = IM.toList <$> resolver M.!? hNm
    mfWords = IM.toList <$> mfResolver M.!? hNm
    flattenMFMap = concat . map snd
    in case (binds , mfWords) of
    (Just [] , _)  -> error $ "impossible: empty imap ?!"
    (Just [(0     , iNm)] , Nothing)-> Imported $ (prevBinds V.! 0) V.! iNm -- resolve prims directly
    (Just [(modNm , iNm)] , Nothing)-> Importable modNm iNm
    (Just [oneBind] , Just mfWords) -> MixfixyVar $ Mixfixy (Just oneBind) (flattenMFMap mfWords)
    (Nothing        , Just mfWords) -> MixfixyVar $ Mixfixy Nothing (flattenMFMap mfWords)
    (Nothing        , Nothing)      -> NotInScope hNm
    (Just many , _)                 -> AmbiguousBinding hNm

  -- convert noScopeNames map to a vector (Map HName IName -> Vector HName)
  names noScopeNames = V.create $ do
    v <- MV.unsafeNew (M.size noScopeNames)
    (\nm idx -> MV.write v idx $ resolveName nm) `M.traverseWithKey` noScopeNames
    pure v

  in (GlobalResolver n resolver prevBinds mfResolver
     , Externs { extNames = names unknownNames , extBinds = prevBinds })

addModule2Resolver (GlobalResolver modCount nameMaps binds mfResolver) newBinds = let
  in GlobalResolver modCount nameMaps (binds `V.snoc` newBinds) mfResolver

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
primBinds :: V.Vector Expr = V.fromList $ snd <$> primTable

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
  ]

[i, bi, b, f, c, ia, str, set , i64] = getPrimTy <$> ["Int", "BigInt" , "Bool", "Double", "Char", "IntArray", "CString", "Set" , "Int64"]

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
  , ("puts"  , (Puts , ([str] , i)))
  , ("putNumber" , (PutNbr , ([i] , i)))
  , ("IntN"  , (TyInstr MkIntN , ([i] , set)))
  , ("primLen" , (Len , ([ia] , i)))
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
  , ("bitOR" , (NumInstr (BitInstr Xor ) , ([i, i] , i) ))
  , ("bitNOT", (NumInstr (BitInstr Not ) , ([i, i] , i) ))
  , ("bitSHL", (NumInstr (BitInstr ShL ) , ([i, i] , i) ))
  , ("bitSHR", (NumInstr (BitInstr ShR ) , ([i, i] , i) ))

  , ("gmp-putNumber" , (GMPPutNbr , ([bi] , i)))
  , ("gmp-add"  , (GMPInstr (IntInstr Add) , ([bi, bi] , bi) ))
  , ("gmp-sub"  , (GMPInstr (IntInstr Sub) , ([bi, bi] , bi) ))
  , ("gmp-mul"  , (GMPInstr (IntInstr Mul) , ([bi, bi] , bi) ))
  ]

typeOfLit = \case
  String{}  -> THPrim $ PtrTo (PrimInt 8) --"CharPtr"
  Array{}   -> THPrim $ PtrTo (PrimInt 8) --"CharPtr"
  PolyInt{} -> THPrim PrimBigInt
  Int{}     -> THPrim (PrimInt 32)
--PolyInt{} -> THPrim (PrimInt 32)
--Int 0     -> THPrim (PrimInt 1)
--Int 1     -> THPrim (PrimInt 1)
--Int{}     -> THPrim (PrimInt 32)
  Char{}    -> THPrim (PrimInt 8) --THExt 3
  x -> error $ "don't know type of literal: " <> show x
