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
import Data.Function
import Data.Foldable
import Control.Lens

-- 1. vector of VNames for parsed NoScope vars
-- 2. extra binds to append to module (tc convenience)
resolveImports :: P.Module -> (V.Vector IName , V.Vector Expr)
resolveImports pm = let
  noScopeNames = pm ^. P.parseDetails . P.hNamesNoScope
  resolveImport :: HName -> IName
   = \nm -> asum
    [ getPrimIdx nm
    , M.lookup nm noScopeNames
    ] & \case
      Just i  -> i
      Nothing -> error $ "not in scope: " ++ show nm

  vNames = V.fromList $ resolveImport <$> M.keys noScopeNames
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

primTys =
 [ ("Bool"   , PrimInt 1)
 , ("Int"    , PrimInt 32)
 , ("Float"  , PrimFloat FloatTy )
 , ("Double" , PrimFloat DoubleTy)
 , ("CharPtr", PtrTo $ PrimInt 8 )
 ]

-- instrs are typed with indexes into the primty map
instrs = let
 i = case M.lookup "Int" primTyMap of
   Nothing -> error "panic: badly setup primtables"
   Just i  -> i
 in
 [ ("+" , (IntInstr Add , ([i, i] , i) ))
 , ("-" , (IntInstr Add , ([i, i] , i) ))
 ]

typeOfLit = \case
  String{}   -> THPrim $ PtrTo (PrimInt 8) --"CharPtr"
  Array{}    -> THPrim $ PtrTo (PrimInt 8) --"CharPtr"
  PolyInt{} -> THPrim (PrimInt 32)
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
