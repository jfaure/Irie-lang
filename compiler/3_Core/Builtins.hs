-- Builtins: the interface to compiler primitives is a (hardcoded) standard importable module
-- * the Prelude supplies mixfixes and more convenient access to many primitives
-- * construct a vector of primitives
-- * supply a (Map HName IName) to resolve names to indexes
module Builtins (primBinds , primMap , typeOfLit) where
import Prim
import CoreSyn
--import CoreUtils
import qualified Data.Map.Strict as M
import qualified Data.Vector as V
import qualified Data.IntMap as IM

mkExtTy x = [THExt x]
getPrimIdx = (primMap M.!?)
getPrimTy nm = case getPrimIdx nm of -- case M.lookup nm primTyMap of
  Nothing -> panic $ "panic: badly setup primtables; " <> nm <> " not in scope"
  Just i  -> i

primMap = M.fromList $ zipWith (\(nm,_val) i -> (nm,i)) primTable [0..]
--primBinds :: V.Vector Expr = V.fromList $ snd <$> primTable
primBinds :: V.Vector (HName , Expr) = V.fromList primTable

primTable = concat
  [ (\(nm , x)         -> (nm , Ty $ TyGround [THPrim x]) )                  <$> primTys
  , let tys2TyHead  (args , t) = TyGround $ mkTyArrow (TyGround . mkExtTy <$> args) (TyGround $ mkExtTy t) in
    (\(nm , (i , tys)) -> (nm , Core (Instr i) (tys2TyHead tys))) <$> primInstrs
  , (\(nm , (i , t))   -> (nm , Core (Instr i) $ TyGround t))                <$> instrs
  , (\(nm , e)         -> (nm , Ty $ TyGround [e]))                          <$> tyFns
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
  , ("CStruct" , PrimCStruct)
  ]

[i, bi, b, f, c, ia, str, set , i64 , dirp , dirent , cstruct] = getPrimTy <$> ["Int", "BigInt" , "Bool", "Double", "Char", "IntArray", "CString", "Set" , "Int64" , "DIR*" , "dirent*" , "CStruct"]

--substPrimTy i = THPrim $ primTyBinds V.! i

-- instrs are typed with indexes into the primty map
tyFns = [
--[ ("IntN" , (THPi [(0,(mkExtTy i))] [THInstr MkIntN [0]] M.empty))
--  ("arrowTycon", (THPi [(0,[THSet 0]),(1,[THSet 0])] [THInstr ArrowTy [0, 1]] M.empty))
    ("Set" , THSet 0)
--  , ("_→_", (ArrowTy , ([set] , set)))
  ]

-- tuples are THProducts with negative indices;
-- this makes typing tuple access far simpler than introducing a new subtyping relation on records
mkTHTuple vs = THTyCon $ THProduct $ IM.fromList (zip (qName2Key . mkQName 0 <$> [0..]) vs)

mkTyArrow args retTy = [THTyCon $ THArrow args retTy]
mkTHArrow args retTy = let singleton x = [x] in mkTyArrow (TyGround . singleton <$> args) (TyGround $ [retTy])

instrs :: [(HName , (PrimInstr , [TyHead]))] = [
--[ ("addOverflow" , (AddOverflow , mkTHArrow [TyGround [THExt i] , TyGround []] (TyGround [])))
--, ("unlink"      , (Unlink , mkTyArrow [[THExt str] , mkTHArrow [THExt c,THExt str] (THExt str)] [THExt str]))
--, ("link"        , (Link , mkTHArrow [THExt c] (THExt str)))
    ("strtol"      , (StrToL  , mkTHArrow [THExt str] (THExt i)))
  , ("mkTuple"     , (MkTuple , [THTyCon $ THTuple mempty]))
  , ("ifThenElse"  , (IfThenE , [THBi 1 $ TyGround $ mkTHArrow [THExt b, THBound 0, THBound 0] (THBound 0) ]))
  , ("getcwd"      , (GetCWD  , [THExt str]))

  -- TODO fix type (set -> set -> A -> B)
  , ("ptr2maybe"   , (Ptr2Maybe , [THBi 2 $ TyGround $ mkTHArrow [THExt set , THExt set , THBound 0] (THBound 0) ]))

   -- (Seed -> (Bool , A , Seed)) -> Seed -> %ptr(A)
  , ("unfoldArray"   , (UnFoldArr , let unfoldRet = (\[x] -> x) $ mkTHArrow [THBound 0] (mkTHTuple $ (\x -> TyGround [x]) <$> [THExt b , THExt c , THBound 0])
      in [THBi 1 $ TyGround $ mkTHArrow [THBound 0 , unfoldRet , THBound 0] (THExt str)]))

  -- %ptr(A) -> (Bool , A , %ptr(A))    == str -> (Bool , char , str)
  , ("nextElem" , (NextElem , mkTHArrow [THExt str] (mkTHTuple $ TyGround <$> [[THExt b] , [THExt c] , [THExt str]]) ))
  , ("toCStruct"       , (ToCStruct       , [THBi 1 $ TyGround $ mkTHArrow [THBound 0] (THExt cstruct)] ))
  , ("toCStructPacked" , (ToCStructPacked , [THBi 1 $ TyGround $ mkTHArrow [THBound 0] (THExt cstruct)] ))
  , ("fromCStruct", (FromCStruct , [THBi 1 $ TyGround $ mkTHArrow [THExt cstruct] (THBound 0)] ))
  , ("fromCStructPacked", (FromCStructPacked , [THBi 1 $ TyGround $ mkTHArrow [THExt cstruct] (THBound 0)] ))

  , ("readFile"  , (ReadFile  , mkTHArrow [THExt str] (THExt str)))
  , ("writeFile" , (WriteFile , mkTHArrow [THExt str] (THExt str)))
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
