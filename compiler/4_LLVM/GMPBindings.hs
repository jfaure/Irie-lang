module GMPBindings where
import Prim2LLVM
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified LLVM.AST as L
import qualified LLVM.AST.Type as LT
import qualified LLVM.AST.Constant as C
import LLVM.AST.Global as L
import LLVM.IRBuilder.Instruction as L

mkGMPDecl = mkExtDecl

mp_bitcnt_t  = i64_t
mpz_struct_t = LT.StructureType False [i32_t , i32_t , LT.ptr i64_t]
mpz_struct_tname = (LT.NamedTypeReference "mpz_struct_t")
mpz_t        = LT.ptr (LT.NamedTypeReference "mpz_struct_t") --mpz_t
mpq_struct_t = LT.StructureType False [mpz_struct_t , mpz_struct_t]
mpq_t        = LT.ptr (LT.NamedTypeReference "mpq_struct_t")

-- careful changing the order in here; it must match vecGMPDecls
init : init_set_str : init_set_ui : init_set_si : init_set_d : sizeinbase : getstr
 : add : add_ui : sub : sub_ui : ui_sub
 : mul : mul_si : mul_ui : addmul : addmul_si : submul : submul_si : mul2exp
 : neg : abs
 : tdiv_q : tdiv_r : tdiv_qr : tdiv_q_ui : tdiv_r_ui : tdiv_qr_ui : tdiv_ui
 : tdiv_q_2exp : tdiv_r_2exp
 : powm : powm_ui : powm_sec : pow_ui : ui_pow_ui
 : root : rootrem : sqrt : sqrtrem : perfect_power : perfect_square_p
 : cmp : cmp_d : cmp_abs : cmp_abs_d : cmp_abs_ui
 : and : or : ior : xor : com : popcount : hamdist
 : scan0 : scan1 : setbit : clrbit : combit : tstbit
 : gmpDeclsLen : _ = [0..] :: [Int]
vecGMPDecls = V.fromList $
 [ mkGMPDecl "__gmpz_init"         [mpz_t] LT.VoidType
 , mkGMPDecl "__gmpz_init_set_str" [mpz_t , charPtr_t , i32_t] i32_t
 , mkGMPDecl "__gmpz_init_set_ui"  [mpz_t , i64_t]         LT.VoidType
 , mkGMPDecl "__gmpz_init_set_si"  [mpz_t , i64_t]         LT.VoidType
 , mkGMPDecl "__gmpz_init_set_d"   [mpz_t , double_t]      LT.VoidType
 , mkGMPDecl "__gmpz_sizeinbase"   [mpz_t , i32_t] i64_t
 , mkGMPDecl "__gmpz_get_str"      [charPtr_t , i32_t , mpz_t] charPtr_t
 -- Integer arithmetic
 , mkGMPDecl "__gmpz_add"          [mpz_t , mpz_t , mpz_t] LT.VoidType
 , mkGMPDecl "__gmpz_add_ui"       [mpz_t , mpz_t , i64_t] LT.VoidType
 , mkGMPDecl "__gmpz_sub"          [mpz_t , mpz_t , mpz_t] LT.VoidType
 , mkGMPDecl "__gmpz_sub_ui"       [mpz_t , mpz_t , i64_t] LT.VoidType
 , mkGMPDecl "__gmpz_ui_sub"       [mpz_t , i64_t , mpz_t] LT.VoidType
 , mkGMPDecl "__gmpz_mul"          [mpz_t , mpz_t , mpz_t] LT.VoidType
 , mkGMPDecl "__gmpz_mul_si"       [mpz_t , mpz_t , i64_t] LT.VoidType
 , mkGMPDecl "__gmpz_mul_ui"       [mpz_t , mpz_t , i64_t] LT.VoidType
 , mkGMPDecl "__gmpz_addmul"       [mpz_t , mpz_t , mpz_t] LT.VoidType -- rop=rop+op1*op2
 , mkGMPDecl "__gmpz_addmul_si"    [mpz_t , mpz_t , i64_t] LT.VoidType
 , mkGMPDecl "__gmpz_submul"       [mpz_t , mpz_t , mpz_t] LT.VoidType -- rop = rop-op1*op2
 , mkGMPDecl "__gmpz_submul_si"    [mpz_t , mpz_t , i64_t] LT.VoidType
 , mkGMPDecl "__gmpz_mul2exp"      [mpz_t , mpz_t , mp_bitcnt_t] LT.VoidType -- rop=op1*2^op2
 , mkGMPDecl "__gmpz_neg"          [mpz_t , mpz_t] LT.VoidType
 , mkGMPDecl "__gmpz_abs"          [mpz_t , mpz_t] LT.VoidType

 -- Division (t => truncate towards 0) (also ceil and floor)
 , mkGMPDecl "__gmpz_tdiv_q"          [mpz_t , mpz_t , mpz_t]         LT.VoidType
 , mkGMPDecl "__gmpz_tdiv_r"          [mpz_t , mpz_t , mpz_t]         LT.VoidType
 , mkGMPDecl "__gmpz_tdiv_qr"         [mpz_t , mpz_t , mpz_t , mpz_t] LT.VoidType
 , mkGMPDecl "__gmpz_tdiv_q_ui"       [mpz_t , mpz_t , i64_t]         i64_t
 , mkGMPDecl "__gmpz_tdiv_r_ui"       [mpz_t , mpz_t , i64_t]         i64_t
 , mkGMPDecl "__gmpz_tdiv_qr_ui"      [mpz_t , mpz_t , mpz_t , i64_t] i64_t
 , mkGMPDecl "__gmpz_tdiv_ui"         [mpz_t , i64_t]                 i64_t
 , mkGMPDecl "__gmpz_tdiv_q_2exp"     [mpz_t , mpz_t , mp_bitcnt_t] LT.VoidType
 , mkGMPDecl "__gmpz_tdiv_r_2exp"     [mpz_t , mpz_t , mp_bitcnt_t] LT.VoidType

 -- exponentiation
 , mkGMPDecl "__gmpz_powm"         [mpz_t , mpz_t , mpz_t , mpz_t] LT.VoidType -- rop base exp mod
 , mkGMPDecl "__gmpz_powm_ui"      [mpz_t , mpz_t , i64_t , mpz_t] LT.VoidType
 , mkGMPDecl "__gmpz_powm_sec"     [mpz_t , mpz_t , mpz_t , mpz_t] LT.VoidType -- crypto
 , mkGMPDecl "__gmpz_pow_ui"       [mpz_t , mpz_t , i64_t] LT.VoidType
 , mkGMPDecl "__gmpz_ui_pow_ui"    [mpz_t , i64_t , i64_t] LT.VoidType

 -- roots
 , mkGMPDecl "__gmpz_root"         [mpz_t , mpz_t , i64_t] i32_t -- non-z if exact comp.
 , mkGMPDecl "__gmpz_rootrem"      [mpz_t , mpz_t , mpz_t , i64_t] LT.VoidType
 , mkGMPDecl "__gmpz_sqrt"         [mpz_t , mpz_t] LT.VoidType
 , mkGMPDecl "__gmpz_sqrtrem"      [mpz_t , mpz_t , mpz_t] LT.VoidType
 , mkGMPDecl "__gmpz_perfect_power"[mpz_t] i32_t -- non-zero if perfect power
 , mkGMPDecl "__gmpz_perfect_square_p"[mpz_t] i32_t -- non-zero if perfect power

 -- number-theoretic functions

 -- comparisons
 , mkGMPDecl "__gmpz_cmp"        [mpz_t , mpz_t] i32_t -- non-zero if perfect power
 , mkGMPDecl "__gmpz_cmp_d"      [mpz_t , double_t] i32_t -- non-zero if perfect power
 , mkGMPDecl "__gmpz_cmp_si"     [mpz_t , i64_t] i32_t -- gmp docs says cmp_si|ui are macros, but seems to be wrong
 , mkGMPDecl "__gmpz_cmp_ui"     [mpz_t , i64_t] i32_t -- ..
 , mkGMPDecl "__gmpz_cmp_abs"    [mpz_t , mpz_t] i32_t -- non-zero if perfect power
 , mkGMPDecl "__gmpz_cmp_abs_d"  [mpz_t , double_t] i32_t -- non-zero if perfect power
 , mkGMPDecl "__gmpz_cmp_abs_ui" [mpz_t , i64_t] i32_t -- non-zero if perfect power

 -- bit and logic
 , mkGMPDecl "__gmpz_and"      [mpz_t , mpz_t , mpz_t] LT.VoidType
 , mkGMPDecl "__gmpz_or"       [mpz_t , mpz_t , mpz_t] LT.VoidType
 , mkGMPDecl "__gmpz_ior"      [mpz_t , mpz_t , mpz_t] LT.VoidType --inclusive-or
 , mkGMPDecl "__gmpz_xor"      [mpz_t , mpz_t , mpz_t] LT.VoidType
 , mkGMPDecl "__gmpz_com"      [mpz_t , mpz_t] LT.VoidType
 , mkGMPDecl "__gmpz_popcount" [mpz_t]         mp_bitcnt_t
 , mkGMPDecl "__gmpz_hamdist"  [mpz_t , mpz_t] mp_bitcnt_t
 -- scans return largest mp_bitcnt_t on failure
 , mkGMPDecl "__gmpz_scan0"    [mpz_t , mp_bitcnt_t] mp_bitcnt_t -- index of first 0
 , mkGMPDecl "__gmpz_scan1"    [mpz_t , mp_bitcnt_t] mp_bitcnt_t -- index of first 1
 , mkGMPDecl "__gmpz_setbit"   [mpz_t , mp_bitcnt_t] LT.VoidType
 , mkGMPDecl "__gmpz_clrbit"   [mpz_t , mp_bitcnt_t] LT.VoidType
 , mkGMPDecl "__gmpz_combit"   [mpz_t , mp_bitcnt_t] LT.VoidType -- complement bit
 , mkGMPDecl "__gmpz_tstbit"   [mpz_t , mp_bitcnt_t] i32_t -- complement bit
 ]

getGMPDecl :: Int -> CGEnv s L.Operand
getGMPDecl iname = let
  mkRef (L.GlobalDefinition f) = let
    argTys = (\(Parameter ty nm at)->ty) <$> fst (parameters f)
    fnTy = LT.FunctionType (L.returnType f) argTys False
    in L.ConstantOperand $ C.GlobalReference (LT.ptr fnTy) (L.name f)
 
  getDecl iname v = MV.read v iname >>= \case
    Just op -> pure $ mkRef op
    Nothing -> let val = vecGMPDecls V.! iname
      in mkRef val <$ MV.write v iname (Just val)

  in gets gmpDecls >>= \case
    Nothing -> MV.replicate gmpDeclsLen Nothing >>= \v -> do
      modify $ \x->x{ gmpDecls = Just v }
      getDecl iname v
    Just  v -> getDecl iname v

--Lit (Int i) -> getRetPtr >>= \r -> lift (GMP.getGMPDecl GMP.init_set_ui) >>= \f ->
--  mkSTGOp r <$ call' f [r , constI64 i]

isGMPStruct = \case { LT.NamedTypeReference "mpz_struct_t" -> True ; _ -> False }

initSRetGMP sret  = lift (getGMPDecl init) >>= \f -> sret <$ call' f [sret]
zext2GMP i retPtr = lift (getGMPDecl init_set_si) >>= \f -> retPtr <$ call' f [retPtr , i]

initGMPFields fTys sret = let
  go i fTy = when (isGMPStruct fTy) (void $ gepTy fTy sret [constI32 0 , constI32 (fromIntegral i)])
  in sret <$ V.imapM go fTys

initGMPInt i retPtr = let base10 = constI32 10 in
  if   i < 2 ^ (64 - 1) -- signed i64 max
  then if i < 0 then lift (getGMPDecl init_set_si) >>= \f -> retPtr <$ call' f [retPtr , constI64 i]
       else lift (getGMPDecl init_set_ui) >>= \f -> retPtr <$ call' f [retPtr , constI64 i]
  else do
  f      <- lift (getGMPDecl init_set_str)
  istrNm <- lift (freshTopName "istr")
  istr   <- lift $ emitArray istrNm (C.Int 8 . toInteger . ord <$>(show i++['\0']))
  retPtr <$ call' f [retPtr , L.ConstantOperand istr , base10]

putNbr i = let base10 = constI32 10 in do
  getSz <- lift (getGMPDecl sizeinbase)
  sz    <- L.add (constI64 2) =<< call' getSz [i , base10] -- base 10!
  buf   <- alloca' i8_t (Just sz)
  toStr <- lift (getGMPDecl getstr)
  toStr `call'` [buf , base10 , i]
  puts  <- lift (getPrimDecl puts)
  puts `call'` [buf]
