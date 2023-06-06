-- Builtins: the interface to compiler primitives is a hardcoded, but otherwise standard importable module
-- ! the Prelude supplies mixfixes and more convenient access to these primitives
-- * constructs a vector of primitives
-- * supplys a (Map HName IName) to resolve names to indexes
module Builtins (primBinds , primMap , typeOfLit , builtinFalse , builtinTrue , builtinFalseQ , builtinTrueQ) where
import Prim
import CoreSyn
import qualified Data.Map.Strict as M ( Map , (!?) , fromList )
import qualified Data.Vector as V ( Vector, fromList , (!) , toList , length )
import qualified BitSetMap as BSM

tHeadToTy t = TyGround [t]

mkExtTy x  = [mkExt x]
--mkExt = THExt -- dodgy optimisation
mkExt i | i <= V.length primTys = THPrim $ snd (primTys V.! i)
mkExt i = THExt i

getPrimTy :: HName -> IName
getPrimTy nm = case primMap M.!? nm of
  Nothing -> panic $ "panic: badly setup primtables; " <> nm <> " not in scope"
  Just i  -> i - 3 -- since this indexes primTys directly, leave space for boolLabel that wants 0.0 and 0.1

primMap = M.fromList $ Prelude.imap (\i (nm,_val) -> (nm,i)) primTable
primBinds :: V.Vector (HName , Expr) = V.fromList primTable

primType2Type x = Core (Ty (TyGround [THPrim x])) (TySet 0)

primTable :: [(HName , Expr)]
primTable = concat
  [ boolLabel -- ! This must come first since explicitly: False = 0.0 and True = 0.1
  , (\(nm , x)         -> (nm , primType2Type x)) <$> V.toList primTys
  , let tys2TyHead  (args , t) = TyGround $ mkTyArrow (TyGround . mkExtTy <$> args) (TyGround $ mkExtTy t) in
    (\(nm , (i , tys)) -> (nm , Core (Instr i) (tys2TyHead tys)))         <$> primInstrs
  , (\(nm , (i , t))   -> (nm , Core (Instr i) (TyGround t)))             <$> instrs
  , [("Set" , Core (Ty (TySet 0)) (TySet 1))]
  , (\(nm , aTs , retT)   -> let
    ty = case aTs of
      []  -> tHeadToTy retT
      aTs -> TyGround [THTyCon (THArrow (tHeadToTy <$> aTs) (tHeadToTy retT))]
    in (nm {-<&> \case { '_' -> '-' ; x -> x }-}
      , Core (X86Intrinsic nm) ty)) <$> x86Intrinsics
-- , (\(nm , e)         -> (nm , Ty (TyGround [e])))                      <$> tyFns
-- , uncurry ExtFn <$> extFnBinds
  ]

mm256 = THPrim (X86Vec 256)
mm128 = THPrim (X86Vec 128)
primI32 = THPrim (PrimInt 32)
-- TODO ? '-' name is replaced by '-' in irie to avoid confusion with mixfixes
x86Intrinsics =
  [ ("_mm256_abs_epi8"     , [mm256] , mm256)
  , ("_mm256_add_epi8"     , [mm256 , mm256] , mm256)
  , ("_mm256_adds_epi8"    , [mm256 , mm256] , mm256)
  , ("_mm256_alignr_epi8"  , [mm256 , mm256 , primI32] , mm256)
  , ("_mm256_blendv_epi8"  , [mm256 , mm256 , mm256] , mm256)
  , ("_mm256_broadcastb_epi8" , [mm128] , mm256)
  , ("_mm256_cmpeq_epi8"  , [mm256 , mm256] , mm256)
  , ("_mm256_cmpgt_epi8"  , [mm256 , mm256] , mm256)
  , ("_mm256_cvtepi8_epi16"  , [mm128] , mm256)
  , ("_mm256_cvtepi8_epi32"  , [mm128] , mm256)
  , ("_mm256_cvtepi8_epi64"  , [mm128] , mm256)
  , ("_mm256_extract_epi8"  , [mm256 , primI32] , primI32)
  , ("_mm256_insert_epi8"  , [mm256 , primI32 , primI32] , mm256)
  , ("_mm256_max_epi8"     , [mm256 , mm256] , mm256)
  , ("_mm256_min_epi8"     , [mm256 , mm256] , mm256)
  , ("_mm256_movemask_epi8" , [mm256] , primI32)
  , ("_mm256_set_epi8" , replicate 32 (THPrim (PrimInt 8)) , mm256)
  , ("_mm256_setr_epi8" , replicate 32 (THPrim (PrimInt 8)) , mm256)
  , ("_mm256_set1_epi8" , [THPrim (PrimInt 8)] , mm256)
  , ("_mm256_shuffle_epi8" , [mm256 , mm256] , mm256)
  , ("_mm256_sign_epi8" , [mm256 , mm256] , mm256)
  , ("_mm256_sub_epi8" , [mm256 , mm256] , mm256)
  , ("_mm256_subs_epi8" , [mm256 , mm256] , mm256)
  , ("_mm256_unpackhi_epi8" , [mm256 , mm256] , mm256)
  , ("_mm256_unpacklo_epi8" , [mm256 , mm256] , mm256)

  , ("_mm256_undefined_si256" , [] , mm256)
  , ("_mm256_permute2x128_si256" , [mm256 , mm256 , primI32] , mm256)
  , ("_mm256_and_si256" , [mm256 , mm256] , mm256)
  , ("_mm256_andnot_si256" , [mm256 , mm256] , mm256)
  , ("_mm256_or_si256" , [mm256 , mm256] , mm256)
  , ("_mm256_xor_si256" , [mm256 , mm256] , mm256)
  , ("_mm256_setzero_si256" , [] , mm256)
  , ("_mm256_slli_si256" , [mm256 , mm256] , mm256)
  , ("_mm256_srli_si256" , [mm256 , mm256] , mm256)
  , ("_mm256_zextsi128_si256" , [mm128] , mm256)
  , ("_mm256_testc_si256" , [mm256 , mm256] , mm256)
  , ("_mm256_testnzc_si256" , [mm256 , mm256] , mm256)
  , ("_mm256_testz_si256" , [mm256 , mm256] , mm256)
  , ("_mm256_castsi128_si256" , [mm128] , mm256)
  , ("_mm256_castsi256_si128" , [mm256] , mm128)
  , ("_mm256_insertf128_si256" , [mm256 , mm128 , primI32] , mm256)
  ]

-- Primitive Labels
-- * Predicates must return labels so if_then_else_ can fuse
boolLabel :: [(HName , Expr)]
boolLabel =
  [ ("False" , Core (Label builtinFalseQ mempty) (TyGround [THTyCon (THSumTy (BSM.fromList [falseLabelT]))]))
  , ("True"  , Core (Label builtinTrueQ  mempty) (TyGround [THTyCon (THSumTy (BSM.fromList [trueLabelT]))]))
  , ("BoolL" , ty (TyGround [boolL]))
  ]
builtinTrue  = Label builtinTrueQ  mempty
builtinFalse = Label builtinFalseQ mempty
builtinFalseQ = mkQName 0 0 -- 0.0
builtinTrueQ = mkQName 0 1 -- 0.1
falseLabelT = (qName2Key builtinFalseQ , TyGround [THTyCon (THTuple mempty)])
trueLabelT  = (qName2Key builtinTrueQ  , TyGround [THTyCon (THTuple mempty)])
boolL       = THTyCon (THSumTy (BSM.fromList [trueLabelT , falseLabelT]))

-- ! Indexes here are of vital importance: THExts are assigned to these to speed up comparisons
-- If anything here is changed, type of lit and the getPrimTy list below may also need to be changed
primTys :: V.Vector (HName , PrimType) = V.fromList
  [ ("Bool"    , PrimInt 1)
  , ("Int"     , PrimInt 32)
  , ("I32"     , PrimInt 64)
  , ("U32"     , PrimNat 64)
  , ("I64"     , PrimInt 64)
  , ("U64"     , PrimNat 64)
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
  , ("m256"    , X86Vec 256)
  , ("m128"    , X86Vec 128)
  ]

--b = boolL
[i, b, f, i8, ia, str, set , i32 , i64 , dirp , _dirent , cstruct , strBuf] = getPrimTy <$> ["Int", "Bool", "Double", "Char", "IntArray", "CString", "Set" , "I32" , "I64" , "DIR*" , "dirent*" , "CStruct" , "StrBuf"]

--substPrimTy i = THPrim $ primTyBinds V.! i

-- instrs are typed with indexes into the primty map
--tyFns = [
--[ ("IntN" , (THPi [(0,(mkExtTy i))] [THInstr MkIntN [0]] M.empty))
--  ("arrowTycon", (THPi [(0,[THSet 0]),(1,[THSet 0])] [THInstr ArrowTy [0, 1]] M.empty))
--  ("Set" , THSet 0)
--  , ("_->_", (ArrowTy , ([set] , set)))
-- ]

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

  , ("newArray"  , (NewArray , [THBi 1 $ TyGround $ mkTHArrow [THExt i64 , THTyCon (THArray (tHeadToTy $ THBound 0))] (THTyCon (THArray (tHeadToTy $ THBound 0)))]))
  , ("readArray"  , (ReadArray , [THBi 1 $ TyGround $ mkTHArrow [THTyCon (THArray (tHeadToTy $ THBound 0)) , THExt i64] (THBound 0)]))
  , ("writeArray" , (WriteArray , [THBi 1 $ TyGround $ mkTHArrow [THTyCon (THArray (tHeadToTy $ THBound 0)) , THExt i64 , THBound 0] (THBound 0)]))

  , ("readFile"  , (ReadFile  , mkTHArrow [mkExt str] (mkExt str)))
  , ("writeFile" , (WriteFile , mkTHArrow [mkExt str , mkExt str] (mkExt i64)))

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
  , ("Fin"   , (TyInstr MkIntN , ([i] , set)))
  , ("primLen" , (Len , ([ia] , i)))

  , ("puts"      , (Puts    , ([str] , i)))
  , ("putNumber" , (PutNbr  , ([i] , i)))
  , ("putChar"   , (PutChar , ([i8] , i8)))
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
--, ("boolOR",  (NumInstr (PredInstr OR )   , ([b, b] , b) ))
--, ("boolAND", (NumInstr (PredInstr AND )  , ([b, b] , b) ))
  , ("zext"  , (Zext  , ([b] , i) ))
  , ("sdiv"  , (NumInstr (IntInstr SDiv) , ([i, i] , i) ))
  , ("srem"  , (NumInstr (IntInstr SRem) , ([i, i] , i) ))
  , ("bitXOR", (NumInstr (BitInstr Xor ) , ([i, i] , i) ))
  , ("bitAND", (NumInstr (BitInstr And ) , ([i, i] , i) ))
  , ("bitANDN", (NumInstr (BitInstr ANDN) , ([i, i] , i) ))
  , ("bitOR" , (NumInstr (BitInstr Or  ) , ([i, i] , i) ))
  , ("bitNOT", (NumInstr (BitInstr Not ) , ([i] , i) ))
  , ("bitSHL", (NumInstr (BitInstr ShL ) , ([i, i] , i) ))
  , ("bitSHR", (NumInstr (BitInstr ShR ) , ([i, i] , i) ))
  , ("bitCLZ", (NumInstr (BitInstr CLZ ) , ([i] , i) ))
  , ("bitCTZ", (NumInstr (BitInstr CTZ ) , ([i] , i) ))
  , ("bitPopCount", (NumInstr (BitInstr PopCount ) , ([i] , i) ))
  , ("bitPDEP", (NumInstr (BitInstr PDEP ) , ([i , i] , i) ))
  , ("bitPEXT", (NumInstr (BitInstr PEXT ) , ([i , i] , i) ))
  ]

typeOfLit = \case
  String{}  -> THPrim $ PtrTo (PrimInt 8) --"CharPtr"
  LitArray{}-> THPrim $ PtrTo (PrimInt 8) --"CharPtr"
  PolyInt{} -> THPrim PrimBigInt
  Int 0     -> THPrim (PrimInt 1)
  Int 1     -> THPrim (PrimInt 1)
  Int{}     -> THPrim (PrimInt 32)
  Char{}    -> THPrim (PrimInt 8)
  Fin n _   -> THPrim (PrimInt n) --mkExt 3
  x -> error $ "don't know type of literal: " <> show x
