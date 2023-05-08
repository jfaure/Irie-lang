module SimplifyInstr where
import CoreSyn
import Prim
import Builtins
import Data.Bits
import qualified Data.Vector as V
import qualified System.Directory as Dir
import System.IO.Unsafe

interpretBinaryIntInstr = \case
  Add  -> (+)
  Mul  -> (*)
  Sub  -> (-)
  SDiv -> div
  SRem -> mod
  IPow -> (^)
  _ -> _
interpretUnaryIntInsrt = \case
 Neg -> \x -> - x
 AbsVal -> abs
 _ -> _
interpretBinaryPredInstr = \case
  EQCmp  -> (==)
  NEQCmp -> (/=)
  LTCmp  -> (< )
  GTCmp  -> (> )
  LECmp  -> (<=)
  GECmp  -> (>=)
  _ -> _
interpretUnaryBitInsrt = \case
  Not -> not
  Complement -> complement
  _ -> _
interpretBinaryBitInstr :: (Num i , Bits i) => BitInstrs -> i -> i -> i
interpretBinaryBitInstr = \case
  Prim.And -> (.&.)
  Or  -> (.|.)
  Prim.Xor -> xor
  _ -> _
--BitRev ->
--ByteSwap ->
-- vv Explicitly require Ints
--ShL -> shiftL
--ShR -> shiftR
--PopCount -> popCount
--CTZ -> countTrailingZeros
--CLZ -> countLeadingZeros
--FShL 
--FShR 
--RotL -> rotateL
--RotR -> rotateR
--TestBit -> testBit
--SetBit  -> setBit
  -- complement
  -- BMI1 & 2

simpleInstr i args = let
--args = args' <&> \case
--  App (Instr j) ars -> simpleInstr j ars
--  x -> x
  in case i of
  IfThenE | [cond , a , b] <- args
          , App pred [Lit (Int x) , Lit (Int y)] <- cond
          , Instr (NumInstr (PredInstr p)) <- pred ->
      if case p of { EQCmp-> x == y ; NEQCmp-> x /= y ; GECmp-> x > y ; GTCmp-> x >= y
                   ; LECmp-> x <= y ; LTCmp-> x < y ; _ -> _ }
      then a else b
  GMPInstr j -> simpleGMPInstr j args
  Zext | [Lit (Int i)]   <- args -> Lit (Fin 64 i)
       | [Lit (Fin _ i)] <- args -> Lit (Fin 64 i)
  NumInstr (IntInstr Chr) | [Lit (Int i) ] <- args -> Lit (Char (chr (fromIntegral i)))
  NumInstr (IntInstr Ord) | [Lit (Char c)] <- args -> Lit (I32  (ord c))
--NumInstr (IntInstr i)  | [Lit (I32 a) , Lit (I32 b)] <- args ->
  NumInstr (IntInstr i)  | [Lit (Int a) , Lit (Int b)] <- args -> Lit (Int (interpretBinaryIntInstr i a b))
  NumInstr (BitInstr i)  | [Lit (Int a) , Lit (Int b)] <- args -> Lit (Int (interpretBinaryBitInstr i a b))
  NumInstr (PredInstr p) | [Lit (Int a) , Lit (Int b)] <- args -> if interpretBinaryPredInstr p a b then builtinTrue else builtinFalse

  -- cannot use posix types directly due to hidden constructors preventing deriving Binary for Literal
  OpenDir | [Lit (String fName)] <- args -> let
    go = Dir.doesDirectoryExist fName >>= \ok -> if ok then Dir.listDirectory fName else pure []
    in Lit (DirStream (unsafePerformIO go))
  ReadDir | [Lit (DirStream fs)] <- args -> case fs of
    []     -> Tuple (V.fromList [builtinFalse , Lit (DirStream []) , Lit (String "")])
    f : fs -> Tuple (V.fromList [builtinTrue  , Lit (DirStream fs) , Lit (String f)])
  IsDir   | [Lit (String fName)] <- args -> if unsafePerformIO (Dir.doesDirectoryExist fName) then builtinTrue else builtinFalse
  Puts    | [Lit (String fName)] <- args -> trace fName $ Lit (Int (fromIntegral $ length fName))

  StrBufToString | [Lit (RevString rs)] <- args -> Lit (String (reverse rs)) -- TODO slow
  PushStrBuf | [Lit (RevString rs) , Lit (Char c)] <- args -> Lit (RevString (c : rs))
  AllocStrBuf | [Lit (Int len)] <- args -> Lit (RevString [])
  _ -> App (Instr i) args

simpleGMPInstr ∷ NumInstrs -> [Term] -> Term
simpleGMPInstr i args = let
  mkCmpInstr pred args = App (Instr (NumInstr (PredInstr pred))) args
  in case i of
  IntInstr Add
    | [Cast (CastInstr (GMPZext _)) (Lit (Int i)) , rarg] <- args -> App (Instr (GMPOther AddUI)) [Lit (Fin 64 i) , rarg]
    | [larg , Cast (CastInstr (GMPZext _)) (Lit (Int i))] <- args -> App (Instr (GMPOther AddUI)) [Lit (Fin 64 i) , larg]
    | _ <- args -> App (Instr (GMPInstr i)) args
  IntInstr Sub
    | [Cast (CastInstr (GMPZext _)) (Lit (Int i)) , rarg] <- args -> App (Instr (GMPOther UISub)) [Lit (Fin 64 i) , rarg]
    | [larg , Cast (CastInstr (GMPZext _)) (Lit (Int i))] <- args -> App (Instr (GMPOther SubUI)) [larg , Lit (Fin 64 i)]
    | _ <- args -> App (Instr (GMPInstr i)) args
  IntInstr Mul
    -- ? MulUI
    | [Lit (Fin 64 _i) , _rarg] <- args -> App (Instr (GMPOther MulSI)) args
    | [larg , Lit (Fin 64 i)]   <- args -> App (Instr (GMPOther MulSI)) [Lit (Fin 64 i) , larg]
  PredInstr LECmp -- TODO other cmp types
    -- CMPAbsD CMPAbsUI
    -- TODO spawn the icmp instruction here
    | [Cast (CastInstr (GMPZext _n)) (Lit (Int i)) , rarg] <- args ->
        mkCmpInstr GECmp [App (Instr (GMPOther CMPUI)) [rarg , Lit (Fin 64 i)] , Lit (Fin 32 0)] -- flip the icmp
    | [larg , Cast (CastInstr (GMPZext _n)) (Lit (Int i))] <- args ->
        mkCmpInstr LECmp [App (Instr (GMPOther CMPUI)) [larg , Lit (Fin 64 i)] , Lit (Fin 32 0)]
  IntInstr IPow
    -- powmui ?
    | [Lit (Fin 64 _) , Lit (Fin 64 _)] <- args -> App (Instr (GMPOther UIPowUI)) args
    | [_larg , Lit (Fin 64 _)]          <- args -> App (Instr (GMPOther PowUI)) args
  -- nothing to fold
  i -> App (Instr (GMPInstr i)) args
