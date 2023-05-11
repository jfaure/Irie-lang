-- Builtins: the interface to compiler primitives is a hardcoded, but otherwise standard importable module
-- ! the Prelude supplies mixfixes and more convenient access to these primitives
-- * constructs a vector of primitives
-- * supplys a (Map HName IName) to resolve names to indexes
module Builtins (primBinds , primMap , typeOfLit , primLabelHNames , primLabelMap , primFieldHNames , primFieldMap , builtinFalse , builtinTrue , builtinFalseQ , builtinTrueQ) where
import Prim
import CoreSyn
import qualified Data.Map.Strict as M ( Map , (!?) , fromList )
import qualified Data.Vector as V ( Vector, fromList , (!) , toList , length )
import qualified BitSetMap as BSM

--mkExtTy x  = [THExt x]
mkExtTy x  = [mkExt x]
getPrimIdx = (primMap M.!?)

getPrimTy :: HName -> IName
getPrimTy nm = case getPrimIdx nm of
  Nothing -> panic $ "panic: badly setup primtables; " <> nm <> " not in scope"
  Just i  -> i

primMap = M.fromList $ zipWith (\(nm,_val) i -> (nm,i)) primTable [0..]
primBinds :: V.Vector (HName , Expr) = V.fromList primTable

primType2Type x = Core (Ty (TyGround [THPrim x])) (TySet 1)
primTable :: [(HName , Expr)]
primTable = concat
  [ (\(nm , x)         -> (nm , primType2Type x)) <$> V.toList primTys
  , boolLabel
  , let tys2TyHead  (args , t) = TyGround $ mkTyArrow (TyGround . mkExtTy <$> args) (TyGround $ mkExtTy t) in
    (\(nm , (i , tys)) -> (nm , Core (Instr i) (tys2TyHead tys)))           <$> primInstrs
  , (\(nm , (i , t))   -> (nm , Core (Instr i) (TyGround t)))               <$> instrs
  , [("Set" , Core (Ty (TySet 0)) (TySet 1))]
-- , (\(nm , e)         -> (nm , Ty (TyGround [e])))                         <$> tyFns
-- , uncurry ExtFn <$> extFnBinds
  ]

-- Primitive Labels
-- * Predicates must return labels so if_then_else_ can fuse
boolLabel :: [(HName , Expr)]
boolLabel =
  [ ("BoolL" , ty (TyGround [boolL]))
  , ("True"  , Core (Label builtinTrueQ  mempty) (TyGround [THTyCon (THSumTy (BSM.fromList [trueLabelT]))]))
  , ("False" , Core (Label builtinFalseQ mempty) (TyGround [THTyCon (THSumTy (BSM.fromList [falseLabelT]))]))
  ]
builtinTrue  = Label builtinTrueQ  mempty
builtinFalse = Label builtinFalseQ mempty
builtinFalseQ = mkQName 0 0 -- 0.0
builtinTrueQ = mkQName 0 1 -- 0.1
falseLabelT = (qName2Key builtinFalseQ , TyGround [THTyCon (THTuple mempty)])
trueLabelT  = (qName2Key builtinTrueQ  , TyGround [THTyCon (THTuple mempty)])
boolL       = THTyCon (THSumTy (BSM.fromList [trueLabelT , falseLabelT]))

primLabelHNames = V.fromList ["False" , "True"] :: V.Vector HName
primLabelMap    = M.fromList [("True" , builtinTrueQ) , ("False" , builtinFalseQ)] :: M.Map HName QName

-- Primitive field Names
primFieldHNames = mempty :: V.Vector HName
primFieldMap    = mempty :: M.Map HName QName

-- ! Indexes here are of vital importance: THExts are assigned to these to speed up comparisons
-- If anything here is changed, type of lit must also change
primTys :: V.Vector (HName , PrimType) = V.fromList
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
  , ("StrBuf"  , PrimStrBuf)
  ]

--b = boolL
[i, bi, b, f, c, ia, str, set , i64 , dirp , _dirent , cstruct , strBuf] = getPrimTy <$> ["Int", "BigInt" , "Bool", "Double", "Char", "IntArray", "CString", "Set" , "Int64" , "DIR*" , "dirent*" , "CStruct" , "StrBuf"]
i8 = c
i32 = i

--substPrimTy i = THPrim $ primTyBinds V.! i

--mkExt = THExt -- dodgy optimisation
mkExt i | i <= V.length primTys = THPrim $ snd (primTys V.! i)
mkExt i = THExt i

-- instrs are typed with indexes into the primty map
tyFns = [
--[ ("IntN" , (THPi [(0,(mkExtTy i))] [THInstr MkIntN [0]] M.empty))
--  ("arrowTycon", (THPi [(0,[THSet 0]),(1,[THSet 0])] [THInstr ArrowTy [0, 1]] M.empty))
--  ("Set" , THSet 0)
--  , ("_->_", (ArrowTy , ([set] , set)))
  ]

-- tuples are THProducts in module 0 (builtin module)
mkTHTuple vs = THTyCon $ THProduct $ BSM.fromList (zip (qName2Key . mkQName 0 <$> [0..]) vs)

mkTyArrow args retTy = [THTyCon $ THArrow args retTy]
mkTHArrow args retTy = let singleton x = [x] in mkTyArrow (TyGround . singleton <$> args) (TyGround $ [retTy])

instrs :: [(HName , (PrimInstr , GroundType))] = [
--[ ("addOverflow"   , (AddOverflow , mkTHArrow [TyGround [mkExt i] , TyGround []] (TyGround [])))
--, ("unlink"        , (Unlink , mkTyArrow [[mkExt str] , mkTHArrow [mkExt c,mkExt str] (mkExt str)] [mkExt str]))
--, ("link"          , (Link , mkTHArrow [mkExt c] (mkExt str)))
    ("strtol"        , (StrToL  , mkTHArrow [mkExt str] (mkExt i)))
  , ("mkTuple"       , (MkTuple , [THTyCon $ THTuple mempty]))
  , ("ifThenElseInt1", (IfThenE , [THBi 1 $ TyGround $ mkTHArrow [mkExt b, THBound 0, THBound 0] (THBound 0) ]))
  , ("getcwd"        , (GetCWD  , [mkExt str]))

  -- TODO fix type (set -> set -> A -> B)
  , ("ptr2maybe"   , (Ptr2Maybe , [THBi 2 $ TyGround $ mkTHArrow [mkExt set , mkExt set , THBound 0] (THBound 0) ]))

   -- (Seed -> (Bool , A , Seed)) -> Seed -> %ptr(A)
--, ("unfoldString"   , (UnFoldStr , let unfoldRet = (\[x] -> x) $ mkTHArrow [THBound 0] (mkTHTuple $ (\x -> TyGround [x]) <$> [mkExt b , mkExt c , THBound 0])
--    in [THBi 1 $ TyGround $ mkTHArrow [THBound 0 , unfoldRet , THBound 0] (mkExt str)]))

---- %ptr(A) -> (Bool , A , %ptr(A))    == str -> (Bool , char , str)
--, ("nextElem" , (NextElem , mkTHArrow [mkExt str] (mkTHTuple $ TyGround <$> [[boolL] , [mkExt c] , [mkExt str]]) ))
  , ("nullString" , (NullString , mkTHArrow [mkExt str] boolL)) -- unCons : String -> (Char , String)
   --unCons : String -> (Char , String)
  , ("unConsString" , (UnCons , mkTHArrow [mkExt str] (mkTHTuple [TyGround [charTy] , TyGround [mkExt str]])))

  , ("toCStruct"       , (ToCStruct       , [THBi 1 $ TyGround $ mkTHArrow [THBound 0] (mkExt cstruct)] ))
  , ("toCStructPacked" , (ToCStructPacked , [THBi 1 $ TyGround $ mkTHArrow [THBound 0] (mkExt cstruct)] ))
  , ("fromCStruct", (FromCStruct , [THBi 1 $ TyGround $ mkTHArrow [mkExt cstruct] (THBound 0)] ))
  , ("fromCStructPacked", (FromCStructPacked , [THBi 1 $ TyGround $ mkTHArrow [mkExt cstruct] (THBound 0)] ))

  , ("allocStrBuf" , (AllocStrBuf , mkTHArrow [iTy] (mkExt strBuf)))
  , ("pushStrBuf" , (PushStrBuf , mkTHArrow [mkExt strBuf , charTy] (mkExt strBuf)))
  , ("strBufToString" , (StrBufToString , mkTHArrow [mkExt strBuf] (mkExt str)))

  , ("readFile"  , (ReadFile  , mkTHArrow [mkExt str] (mkExt str)))
  , ("writeFile" , (WriteFile , mkTHArrow [mkExt str] (mkExt str)))

  , ("opendir" , (OpenDir , mkTHArrow [mkExt str]  (mkExt dirp)))
  , ("readdir" , (ReadDir , mkTHArrow [mkExt dirp] (mkTHTuple $ TyGround <$> [[boolL] , [mkExt dirp] , [mkExt str]] )))
  , ("isdir"   , (IsDir   , mkTHArrow [mkExt str] boolL))

--, ("fcmp"  , (NumInstr (FracInstr FCmp  ) , ([f, f] , b) ))
  , ("le"      , (NumInstr (PredInstr LECmp ) , mkTHArrow [iTy , iTy]    boolL))
  , ("ge"      , (NumInstr (PredInstr GECmp ) , mkTHArrow [iTy , iTy]    boolL))
  , ("lt"      , (NumInstr (PredInstr LTCmp ) , mkTHArrow [iTy , iTy]    boolL))
  , ("gt"      , (NumInstr (PredInstr GTCmp ) , mkTHArrow [iTy , iTy]    boolL))
  , ("eq"      , (NumInstr (PredInstr EQCmp ) , mkTHArrow [iTy , iTy]    boolL))
  , ("ne"      , (NumInstr (PredInstr NEQCmp) , mkTHArrow [iTy , iTy]    boolL))
  , ("boolOR"  , (NumInstr (PredInstr OR )   , mkTHArrow [boolL, boolL] boolL))
  , ("boolAND" , (NumInstr (PredInstr AND )   , mkTHArrow [boolL, boolL] boolL))
  ]
iTy = THPrim (PrimInt 32)
charTy = THPrim (PrimInt 8)

primInstrs :: [(HName , (PrimInstr , ([IName] , IName)))] =
  [ ("Arrow" , (TyInstr Arrow  , ([set,set] , set)))
  , ("IntN"  , (TyInstr MkIntN , ([i] , set)))
  , ("primLen" , (Len , ([ia] , i)))

  , ("puts"      , (Puts    , ([str] , i)))
  , ("putNumber" , (PutNbr  , ([i] , i)))
  , ("putChar"   , (PutChar , ([c] , c)))
  , ("ord"       , (NumInstr (IntInstr Ord) , ([i8] , i32)))
  , ("chr"       , (NumInstr (IntInstr Chr) , ([i32] , i8)))

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
--, ("fcmp"  , (NumInstr (FracInstr FCmp  ) , ([f, f] , b) ))
--, ("le"    , (NumInstr (PredInstr LECmp ) , ([i, i] , b) ))
--, ("ge"    , (NumInstr (PredInstr GECmp ) , ([i, i] , b) ))
--, ("lt"    , (NumInstr (PredInstr LTCmp ) , ([i, i] , b) ))
--, ("gt"    , (NumInstr (PredInstr GTCmp ) , ([i, i] , b) ))
--, ("eq"    , (NumInstr (PredInstr EQCmp ) , ([i, i] , b) ))
--, ("ne"    , (NumInstr (PredInstr NEQCmp) , ([i, i] , b) ))
--, ("boolOR",  (NumInstr (PredInstr OR )   , ([b, b] , b) ))
--, ("boolAND", (NumInstr (PredInstr AND )  , ([b, b] , b) ))
  , ("zext"  , (Zext  , ([b] , i) ))
  , ("sdiv"  , (NumInstr (IntInstr SDiv) , ([i, i] , i) ))
  , ("srem"  , (NumInstr (IntInstr SRem) , ([i, i] , i) ))
  , ("bitXOR", (NumInstr (BitInstr Xor ) , ([i, i] , i) ))
  , ("bitAND", (NumInstr (BitInstr And ) , ([i, i] , i) ))
  , ("bitOR" , (NumInstr (BitInstr Or  ) , ([i, i] , i) ))
  , ("bitNOT", (NumInstr (BitInstr Not ) , ([i, i] , i) ))
  , ("bitSHL", (NumInstr (BitInstr ShL ) , ([i, i] , i) ))
  , ("bitSHR", (NumInstr (BitInstr ShR ) , ([i, i] , i) ))
  , ("bitCLZ", (NumInstr (BitInstr CLZ ) , ([i] , i) ))
  , ("bitCTZ", (NumInstr (BitInstr CTZ ) , ([i] , i) ))
  , ("bitPopCount", (NumInstr (BitInstr PopCount ) , ([i] , i) ))
  , ("bitPDEP", (NumInstr (BitInstr PDEP ) , ([i , i] , i) ))
  , ("bitPEXT", (NumInstr (BitInstr PEXT ) , ([i , i] , i) ))

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
  Char{}    -> THPrim (PrimInt 8) --mkExt 3
  x -> error $ "don't know type of literal: " <> show x
