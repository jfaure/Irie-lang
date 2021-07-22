-- Externs:
-- resolve things that were out of scope when parsed
-- * things in scope, but defined later
-- * primitives: (note. prim bindings are CoreSyn)
-- * imported modules
-- * extern functions (esp. C)

module Externs (GlobalResolver(..) , addModule2Resolver , primResolver , primBinds , Import(..) , Externs(..) , readParseExtern , readPrimExtern , resolveImports , typeOfLit)
where
import Prim
import qualified ParseSyntax as P
import CoreSyn
import ShowCore()

import qualified Data.Map as M
import qualified Data.IntMap as IM
import qualified Data.Text as T
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
   modCount :: Int
 , globalNameMap :: M.Map HName (IM.IntMap IName)
 , allBinds :: V.Vector (V.Vector Expr)
} deriving Show
primResolver :: GlobalResolver = GlobalResolver 1 (IM.singleton 0 <$> primMap) (V.singleton primBinds)

-------------
-- Externs --
-------------
-- 1. vector of VNames for primitives and parsed NoScope vars
-- 2. extra binds available in module (via VarExt names)
data Externs = Externs {
   extNames   :: V.Vector (IName , IName) -- index permuation for noscopeNames
 , extBinds   :: V.Vector (V.Vector Expr) -- extern table indexed by extNames
} deriving Show

-- exported functions to resolve ParseSyn.VExterns
-- ! 'ext names' may in fact be local forward references
readParseExtern = \(Externs nms binds) i -> let (modNm , iNm) = nms V.! i
  in if modNm >= V.length binds
  then Left    iNm
  else Right $ (binds V.! modNm) V.! iNm
readPrimExtern e i = (extBinds e V.! 0) V.! i

-- We need to resolve INames accross module boundaries.
-- Externs are a vector of CoreExprs, generated as: builtins ++ concat imports;
-- which is indexed by the permuation described in the extNames vector.
-- * primitives must always be present in GlobalResolver
resolveImports :: GlobalResolver -> M.Map HName IName -> M.Map HName IName -> (GlobalResolver , Externs)
resolveImports (GlobalResolver n curResolver prevBinds) localNames unknownNames = let
--allBinds = prevAllBinds V.++ V.fromList (fmap (bind2Expr . snd) . importBinds <$> imports)
--allBinds = prevAllBinds `V.snoc` imported ---- V.++ V.fromList (fmap (bind2Expr . snd) . importBinds <$> imports)

  resolver :: M.Map HName (IM.IntMap IName)
  resolver = M.unionWith IM.union curResolver $ M.unionsWith IM.union $
    zipWith (\modNm map -> (\iNm -> IM.singleton modNm iNm) <$> map)
    [n..] [localNames]
 
  resolveName :: HName -> (IName , IName)
  resolveName hNm = case IM.toList <$> resolver M.!? hNm of
    Just [i] -> i
    Just []  -> error $ "empty imap ?!"
    Nothing  -> error $ "not in scope: " ++ T.unpack hNm
    _        -> error $ "ambiguous name: " ++ T.unpack hNm

  -- convert noScopeNames map to a vector (Map HName IName -> Vector HName)
  -- order is messed up, so we fill the names vector index by index
  names noScopeNames = V.create $ do
    v <- MV.unsafeNew (M.size noScopeNames)
    (\nm idx -> MV.write v idx $ resolveName nm) `M.traverseWithKey` noScopeNames
    pure v

  -- during typechecking / type judging, how to find externs
  exts = Externs { extNames = names unknownNames , extBinds = prevBinds }

  -- system-wide modules currently loaded
  in (GlobalResolver n resolver prevBinds
     , exts)

addModule2Resolver (GlobalResolver modCount nameMaps binds) newBinds = let
  in GlobalResolver modCount nameMaps (binds `V.snoc` newBinds)

mkExtTy x = [THExt x]
---------------------------
-- Primitives / Builtins --
---------------------------
-- We prefer INames over inlining primitives
-- * construct a vector of primitives
-- * supply a (Map HName IName) to resolve names to indexes
primMap = M.unions [ primTyMap , instrMap , tyFnMap , instrMap2] --extFnMap
primBinds :: V.Vector Expr = let
 primTy2Expr x = Ty [THPrim x]
 instr2Expr  (e , tys)  = Core (Instr e) [tys2TyHead tys]
 tys2TyHead  (args , t) = THArrow (mkExtTy <$> args) (mkExtTy t)
-- tys2TyHead  (args , t) = THArrow ((\x->[x]) . substPrimTy <$> args) (mkExtTy t)
 tyFn2Expr   (e) = Ty [e]
 in V.concat
   [ primTy2Expr <$> primTyBinds
   , instr2Expr  <$> instrBinds
   , (\(i , t) -> Core (Instr i) t) <$> instrBinds2
   , tyFn2Expr   <$> tyInstrBinds
-- , uncurry ExtFn  <$> extFnBinds
   ]

getPrimIdx nm = M.lookup nm primMap

(primTyMap , primTyBinds, sz0) = buildMaps 0 primTys
(instrMap  , instrBinds , sz1) = buildMaps sz0 instrs
(instrMap2 , instrBinds2, sz2) = buildMaps (sz0 + sz1) instrs2
(tyFnMap , tyInstrBinds , sz3) = buildMaps (sz0 + sz1 + sz2) tyFns
--(extFnMap , extFnBinds  , sz4) = buildMaps (sz0 + sz1 + sz2 + sz3) extFns

buildMaps :: Int -> [(HName , a)] -> (M.Map HName Int , V.Vector a , Int)
buildMaps offset list = let
  vec   = V.fromList $ snd <$> list
  replaceSnd (a,_) i = (a,i)
  nmMap = M.fromList $ zipWith replaceSnd list [(offset::Int)..]
  in (nmMap , vec , M.size nmMap)

primTys :: [(HName , PrimType)] =
  [ ("Bool"    , PrimInt 1)
  , ("Int"     , PrimInt 32)
  , ("Int64"   , PrimInt 64)
  , ("Char"    , PrimInt 8)
  , ("Nat"     , PrimNat 32)
  , ("Float"   , PrimFloat FloatTy )
  , ("Double"  , PrimFloat DoubleTy)
  , ("CharPtr" , PtrTo $ PrimInt 8 )
  , ("IntArray", PrimArr $ PrimInt 32)
  ]
getPrimTy nm = case getPrimIdx nm of -- case M.lookup nm primTyMap of
  Nothing -> error $ "panic: badly setup primtables; "
    ++ T.unpack nm ++ " not in scope"
  Just i  -> i

[i, b, c, ia, str, set , i64] = getPrimTy <$> ["Int", "Bool", "Char", "IntArray", "CharPtr", "Set" , "Int64"]

substPrimTy i = THPrim $ primTyBinds V.! i

-- instrs are typed with indexes into the primty map
tyFns = [
--[ ("IntN" , (THPi [(0,(mkExtTy i))] [THInstr MkIntN [0]] M.empty))
--  ("--->", (THPi [(0,[THSet 0]),(1,[THSet 0])] [THInstr ArrowTy [0, 1]] M.empty))
    ("Set" , THSet 0)
--  , ("_→_", (ArrowTy , ([set] , set)))
  ]

--extFns :: [(HName , (HName , Type))] =
--[ ("printf" , ("printf" , [THArrow (mkExtTy str : repeat []) (mkExtTy i)]))
--[ ("printf" , ("printf" , [THArrow [mkExtTy str] (mkExtTy i)]))
--, ("strtol" , ("strtol" , [THArrow [mkExtTy str , mkExtTy str , mkExtTy i] (mkExtTy i)]))
--]

instrs2 :: [(HName , (PrimInstr , Type))] =
  [ --("ifThenE"     , (IfThenE , [THArrow [[THExt b] , [THExt set] , [THExt set]] [THExt set]]))
    ("addOverflow" , (AddOverflow , [THArrow [[THExt i] , []] []]))
  , ("unlink"      , (Unlink , [THArrow [[THExt str] , [THArrow [[THExt c],[THExt str]] [THExt str]]] [THExt str] ]))
  , ("link"        , (Link , [THArrow [[THExt c]] [THExt str]]))
  , ("strtol"      , (StrToL , [THArrow [[THExt str]] [THExt i]]))
  , ("mkTuple"     , (MkTuple , [THTuple mempty]))
--, ("ifE"         , (IfThenE , [THPi $ Pi [(0,[THSet 0])] [THArrow [[THExt b], [THVar 0]] [THVar 0]] ] ))
  , ("ifE"         , (IfThenE , [THBi 1 $ [THArrow [[THExt b], [THBound 0] , [THBound 0]] [THBound 0]] ] ))

--  ("--->", (THPi [(0,[THSet 0]),(1,[THSet 0])] [THInstr ArrowTy [0, 1]] M.empty))
--
--nub a str = unlink str (nub a str) (\c str => ifThenE (eq c a) str (link c str))

  ]

instrs :: [(HName , (PrimInstr , ([IName] , IName)))] =
  [ ("_+_" , (IntInstr Add  , ([i, i] , i) ))
  , ("_-_" , (IntInstr Sub  , ([i, i] , i) ))
  , ("plus", (IntInstr Add  , ([i, i] , i) ))
  , ("plus64", (IntInstr Add  , ([i64, i64] , i64) ))
  , ("sub" , (IntInstr Sub  , ([i, i] , i) ))
  , ("le" , (PredInstr LECmp , ([i, i] , b) ))
  , ("ge" , (PredInstr GECmp , ([i, i] , b) ))
  , ("eq" , (PredInstr EQCmp , ([i, i] , b) ))
  , ("_!_" , (MemInstr ExtractVal , ([ia, i] , i) ))
  , ("->",   (TyInstr Arrow , ([set,set] , set)))
  , ("IntN", (TyInstr MkIntN , ([i] , set)))
  , ("zext", (Zext  , ([b] , i) ))
  , ("primLen" , (Len , ([ia] , i)))
  , ("putNumber" , (PutNbr , ([i] , i)))
  ]

typeOfLit = \case
  String{}   -> THPrim $ PtrTo (PrimInt 8) --"CharPtr"
  Array{}    -> THPrim $ PtrTo (PrimInt 8) --"CharPtr"
  PolyInt{}  -> THPrim (PrimInt 32)
  Int 0      -> THPrim (PrimInt 1)
  Int 1      -> THPrim (PrimInt 1)
  Int{}      -> THPrim (PrimInt 32)
  Char{}     -> THPrim (PrimInt 8) --THExt 3
  x -> error $ "littype: " ++ show x
--  _ -> numCls

-- TODO (more builtin instructions)
{-
primInstr :: Parser PrimInstr
primInstr = (<?> "Builtin Instr") $
  primDef *> choice
  [ IntInstr   <$> intInstr
  , NatInstr   <$> natInstr
  , FracInstr  <$> fracInstr
  , MemInstr   <$> arrayInstr
  , MkTuple    <$  reserved "MkTuple"
  , Alloc      <$  reserved "alloc"
  , SizeOf     <$  reserved "sizeof"
  ]
  where
  intInstr = choice
    [ symbol "add"  $> Add
    , symbol "sub"  $> Sub
    , symbol "mul"  $> Mul
    , symbol "sdiv" $> SDiv
    , symbol "srem" $> SRem
    , symbol "icmp" $> ICmp
    , symbol "and"  $> And
    , symbol "or"   $> Or
    , symbol "xor"  $> Xor
    , symbol "shl"  $> Shl 
    , symbol "shr"  $> Shr]
  natInstr = choice
    [symbol "udiv" $> UDiv
    , symbol "urem" $> URem]
  fracInstr = choice
    [ symbol "fadd"  $> FAdd
    , symbol "fsub"  $> FSub
    , symbol "fmul"  $> FMul
    , symbol "fdiv"  $> FDiv
    , symbol "frem"  $> FRem
    , symbol "fcmp"  $> FCmp]
  arrayInstr = choice
    [ symbol "gep"         $> Gep
    , symbol "extractVal"  $> ExtractVal
    , symbol "insertVal"   $> InsertVal]
-}
