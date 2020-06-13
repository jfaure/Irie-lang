-- Externs:
-- resolve things that were out of scope when parsed
-- * things in scope, but defined later
-- * primitives: (note. prim bindings are CoreSyn)
-- * imported modules
-- * extern functions (esp. C)

module Externs where
import Prim
import qualified ParseSyntax as P
import CoreSyn

import Control.Applicative
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import Data.Function
import Data.Functor
import Data.Foldable
import Data.List
import Control.Lens hiding (set)
import Debug.Trace

-----------------
-- Import Tree --
-----------------
-- Imports are typechecked binds + parsed nameMap
data Import = Import {
    importNames :: P.NameMap
  , importBinds :: CoreBinds
}
type ImportTree = M.Map HName Import

-------------
-- Externs --
-------------
-- 1. vector of VNames for parsed NoScope vars
-- 2. extra binds available in module (via VarExt names)
data Externs = Externs {
   extNames :: V.Vector IName -- index permuation for noscopeNames
 , extBinds :: V.Vector Expr  -- extern table indexed by extNames
}

-- exported functions to resolve ParseSyn.VExterns
readParseExtern , readExtern :: Externs -> IName -> Expr
readParseExtern = \(Externs nms binds) i -> binds V.! (nms V.! i)
readExtern = \(Externs nms binds) i -> binds V.! i

-- We need to resolve INames accross module boundaries.
-- Externs are a vector of CoreExprs, generated as: builtins ++ concat imports;
-- which is indexed by the permuation described in the extNames vector.
resolveImports :: [Import] -> P.Module -> Externs
resolveImports imports pm = let
  importedExprs = bind2Expr <$> V.concat (importBinds <$> imports)
  -- offset into the final extern table for each import
  offsets       = scanl (+) (V.length primBinds) (V.length . importBinds <$> imports)

  getImportIdx nm = let -- exploiting laziness to add the right offset:
    searchAll = M.lookup nm . importNames <$> imports
    in asum $ zipWith (\off x -> (off+) <$> x) offsets searchAll

  resolveName :: HName -> IName = \nm ->
    asum [ getPrimIdx nm , getImportIdx nm ] & \case
      Just i  -> i
      Nothing -> error $ "not in scope: " ++ T.unpack nm

  -- the noScopeNames map has a messed up order
  -- so we fill the names vector index by index
  names noScopeNames = let
    doIndx v (nm , indx) = MV.write v indx $ resolveName nm
    in V.create $ do
      v <- MV.unsafeNew (M.size noScopeNames)
      doIndx v `mapM` M.toList noScopeNames
      pure v
  in Externs
    { extNames = names (pm ^. P.parseDetails . P.hNamesNoScope)
    , extBinds = primBinds V.++ importedExprs }

---------------------------
-- Primitives / Builtins --
---------------------------
-- We prefer INames over inlining primitives
-- * construct a vector of primitives
-- * supply a (Map HName IName) to resolve names to indexes
primBinds :: V.Vector Expr = let
 primTy2Expr x = Ty [THPrim x]
 instr2Expr  (e , tys)  = Core (Instr e) [tys2TyHead tys]
 tys2TyHead  (args , t) = THArrow ((\x->[THExt x]) <$> args) [THExt t]
 tyFn2Expr   (e) = Ty [e]
 in V.concat
   [ primTy2Expr <$> primTyBinds
   , instr2Expr  <$> instrBinds
   , tyFn2Expr   <$> tyInstrBinds
   ]

getPrimIdx nm = asum
 [ M.lookup nm primTyMap
 , (M.size primTyMap +) <$> M.lookup nm instrMap
 , (M.size primTyMap + M.size instrMap + ) <$> M.lookup nm tyFnMap
 ]

(primTyMap , primTyBinds)   = buildMaps primTys
(instrMap  , instrBinds)    = buildMaps instrs
(tyFnMap , tyInstrBinds) = buildMaps tyFns

buildMaps :: [(HName , a)] -> (M.Map HName Int , V.Vector a)
buildMaps list = let
  vec   = V.fromList $ snd <$> list
  replaceSnd (a,_) i = (a,i)
  nmMap = M.fromList $ zipWith replaceSnd list [(0::Int)..]
  in (nmMap , vec)

primTys :: [(HName , PrimType)] =
  [ ("Bool"    , PrimInt 1)
  , ("Int"     , PrimInt 32)
  , ("Nat"     , PrimNat 32)
  , ("Float"   , PrimFloat FloatTy )
  , ("Double"  , PrimFloat DoubleTy)
  , ("CharPtr" , PtrTo $ PrimInt 8 )
  , ("IntArray", PrimArr $ PrimInt 32)
  ]
getPrimTy nm = case M.lookup nm primTyMap of
  Nothing -> error $ "panic: badly setup primtables; "
    ++ T.unpack nm ++ " not in scope"
  Just i  -> i

[i, b, ia, set] = getPrimTy <$> ["Int", "Bool", "IntArray", "Set"]

-- instrs are typed with indexes into the primty map
tyFns =
  [ ("IntN" , (THPi [(0,[THExt i])] [THInstr MkIntN [0]] M.empty))
  , ("->", (THPi [(0,[THSet 0]),(1,[THSet 0])] [THInstr ArrowTy [0, 1]] M.empty))
  , ("Set" , THSet 0)
--  , ("_→_", (ArrowTy , ([set] , set)))
  ]
instrs :: [(HName , (PrimInstr , ([IName] , IName)))] =
  [ ("primLen" , (Len , ([ia] , i)))
  ] ++ instrsMixFix
instrsMixFix :: [(HName , (PrimInstr , ([IName] , IName)))] =
  [ ("_+_" , (IntInstr Add  , ([i, i] , i) ))
  , ("plus", (IntInstr Add  , ([i, i] , i) ))
  , ("_-_" , (IntInstr Sub  , ([i, i] , i) ))
  , ("_<_" , (IntInstr ICmp , ([i, i] , b) ))
  , ("_!_" , (MemInstr ExtractVal , ([ia, i] , i) ))

--  , ("->", (ArrowTy , ([set] , set)))
  ]

typeOfLit = \case
  String{}   -> THPrim $ PtrTo (PrimInt 8) --"CharPtr"
  Array{}    -> THPrim $ PtrTo (PrimInt 8) --"CharPtr"
  PolyInt{}  -> THPrim (PrimInt 32)
  Int{}      -> THPrim (PrimInt 32)
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
