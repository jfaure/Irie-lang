-- Externs:
-- resolve things that were out of scope when parsed
-- * things in scope, but defined later
-- * primitives: (note. prim bindings are CoreSyn)
-- * externs (in scope via import declarations)
-- * additionally, handle Core primitives (types etc..)

module Externs where
import Prim
import qualified ParseSyntax as P
import CoreSyn
import TCState

import Control.Applicative
import qualified Data.Map as M
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as V
import Data.Function
import Data.Functor
import Data.Foldable
import Data.List
import Control.Lens
import Debug.Trace

-- 1. vector of VNames for parsed NoScope vars
-- 2. extra binds to append to module (tc convenience)
resolveImports :: P.Module -> (V.Vector IName , V.Vector Expr)
resolveImports pm = let
  noScopeNames = pm ^. P.parseDetails . P.hNamesNoScope
  resolveImport :: HName -> IName
   = \nm -> asum
    [ getPrimIdx nm
--  , M.lookup nm noScopeNames -- need to import all noScopeNames first
    ] & \case
      Just i  -> i
      Nothing -> error $ "not in scope: " ++ show nm

  -- the noScopeNames map will have mixed up the iname ordering
  -- no problem; we fill the vNames vector in the same 'random' order
  vNames = let
    doIndx v (nm , indx) = V.write v indx $ resolveImport nm
    in V.create $ do
      v <- V.unsafeNew (M.size noScopeNames)
      doIndx v `mapM` M.toList noScopeNames
      pure v
  in ( vNames
     , primBinds )

-- Primitives
-- We vastly prefer handling INames over inlining primitives
-- * construct a vector of primitives
-- * supply a (Map HName IName) to resolve names to indexes
primBinds = let
 primTy2Expr x = Ty [THPrim x]
 instr2Expr  (e , tys)  = Core (Instr e) [tys2TyHead tys]
 tys2TyHead  (args , t) = THArrow ((\x->[THExt x]) <$> args) [THExt t]
 in V.concat
   [ primTy2Expr <$> primTyBinds
   , instr2Expr  <$> instrBinds
   ]

getPrimIdx nm = asum
 [ M.lookup nm primTyMap
 , (M.size primTyMap +) <$> M.lookup nm instrMap
 ]

(primTyMap , primTyBinds) = buildMaps primTys
(instrMap  , instrBinds)  = buildMaps instrs

buildMaps :: [(HName , a)] -> (M.Map HName Int , V.Vector a)
buildMaps list = let
  vec   = V.fromList $ snd <$> list
  replaceSnd (a,_) i = (a,i)
  nmMap = M.fromList $ zipWith replaceSnd list [(0::Int)..]
  in (nmMap , vec)

primTys :: [(HName , PrimType)] =
  [ ("Bool"    , PrimInt 1)
  , ("Int"     , PrimInt 32)
  , ("Float"   , PrimFloat FloatTy )
  , ("Double"  , PrimFloat DoubleTy)
  , ("CharPtr" , PtrTo $ PrimInt 8 )
  , ("IntArray", PrimArr $ PrimInt 32)
  , ("Set"     , PrimSet)
  ]
getPrimTy nm = case M.lookup nm primTyMap of
  Nothing -> error $ "panic: badly setup primtables; "
    ++ show nm ++ " not in scope"
  Just i  -> i

-- instrs are typed with indexes into the primty map
instrs :: [(HName , (PrimInstr , ([IName] , IName)))] = let
  i   = getPrimTy "Int"
  ia  = getPrimTy "IntArray"
  set = getPrimTy "Set"
  in
  [ ("+" , (IntInstr Add , ([i, i] , i) ))
  , ("-" , (IntInstr Add , ([i, i] , i) ))
  , ("!" , (MemInstr ExtractVal , ([ia] , i) ))
  , ("->", (ArrowTy , ([set] , set)))
  ]

typeOfLit = \case
  String{}   -> THPrim $ PtrTo (PrimInt 8) --"CharPtr"
  Array{}    -> THPrim $ PtrTo (PrimInt 8) --"CharPtr"
  PolyInt{}  -> THPrim (PrimInt 32)
  x -> error $ "littype: " ++ show x
--  _ -> numCls

-- TODO
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
