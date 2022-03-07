module SimplifyInstr where
import CoreSyn
import Prim

simpleInstr i args = case i of
  IfThenE | [cond , a , b] <- args
          , App pred [Lit (Int x) , Lit (Int y)] <- cond -> case pred of
    Instr (NumInstr (PredInstr p)) -> 
      if case p of { EQCmp-> x == y ; NEQCmp-> x /= y ; GECmp-> x > y ; GTCmp-> x >= y ; LECmp-> x <= y ; LTCmp-> x < y }
      then a else b
  GMPInstr j -> simpleGMPInstr j args
  Zext | [Lit (Int i)]   <- args -> Lit (Fin 64 i)
       | [Lit (Fin n i)] <- args -> Lit (Fin 64 i)
  i -> App (Instr i) args

simpleGMPInstr :: NumInstrs -> [Term] -> Term
simpleGMPInstr i args = let
  mkCmpInstr pred args = App (Instr (NumInstr (PredInstr pred))) args
  in case i of
  IntInstr Add
    | [Cast (CastInstr (GMPZext n)) (Lit (Int i)) , rarg] <- args -> App (Instr (GMPOther AddUI)) [Lit (Fin 64 i) , rarg]
    | [larg , Cast (CastInstr (GMPZext n)) (Lit (Int i))] <- args -> App (Instr (GMPOther AddUI)) [Lit (Fin 64 i) , larg]
    | _ <- args -> App (Instr (GMPInstr i)) args
  IntInstr Sub
    | [Cast (CastInstr (GMPZext n)) (Lit (Int i)) , rarg] <- args -> App (Instr (GMPOther UISub)) [Lit (Fin 64 i) , rarg]
    | [larg , Cast (CastInstr (GMPZext n)) (Lit (Int i))] <- args -> App (Instr (GMPOther SubUI)) [larg , Lit (Fin 64 i)]
    | _ <- args -> App (Instr (GMPInstr i)) args
  IntInstr Mul
    -- ? MulUI
    | [Lit (Fin 64 i) , rarg] <- args -> App (Instr (GMPOther MulSI)) args
    | [larg , Lit (Fin 64 i)] <- args -> App (Instr (GMPOther MulSI)) [Lit (Fin 64 i) , larg]
  PredInstr LECmp -- TODO other cmp types
    -- CMPAbsD CMPAbsUI
    -- TODO spawn the icmp instruction here
    | [Cast (CastInstr (GMPZext n)) (Lit (Int i)) , rarg] <- args ->
        mkCmpInstr GECmp [App (Instr (GMPOther CMPUI)) [rarg , Lit (Fin 64 i)] , Lit (Fin 32 0)] -- flip the icmp
    | [larg , Cast (CastInstr (GMPZext n)) (Lit (Int i))] <- args ->
        mkCmpInstr LECmp [App (Instr (GMPOther CMPUI)) [larg , Lit (Fin 64 i)] , Lit (Fin 32 0)]
  IntInstr IPow
    -- powmui ?
    | [Lit (Fin 64 _) , Lit (Fin 64 _)] <- args -> App (Instr (GMPOther UIPowUI)) args
    | [larg , Lit (Fin 64 _)]           <- args -> App (Instr (GMPOther PowUI)) args
  -- nothing to fold
  i -> App (Instr (GMPInstr i)) args
