module SimplifyInstr where
import CoreSyn
import Prim

simpleInstr i args = case i of
  IfThenE | [cond , a , b] ← args
          , App pred [Lit (Int x) , Lit (Int y)] ← cond
          , Instr (NumInstr (PredInstr p)) ← pred →
      if case p of { EQCmp→ x == y ; NEQCmp→ x /= y ; GECmp→ x > y ; GTCmp→ x >= y ; LECmp→ x <= y ; LTCmp→ x < y }
      then a else b
  GMPInstr j → simpleGMPInstr j args
  Zext | [Lit (Int i)]   ← args → Lit (Fin 64 i)
       | [Lit (Fin _ i)] ← args → Lit (Fin 64 i)
  NumInstr (IntInstr Add) | [Lit (I32 a) , Lit (I32 b)] <- args -> Lit (I32 (a + b))
  NumInstr (IntInstr Mul) | [Lit (I32 a) , Lit (I32 b)] <- args -> Lit (I32 (a * b))
  _ -> App (Instr i) args

simpleGMPInstr ∷ NumInstrs → [Term] → Term
simpleGMPInstr i args = let
  mkCmpInstr pred args = App (Instr (NumInstr (PredInstr pred))) args
  in case i of
  IntInstr Add
    | [Cast (CastInstr (GMPZext _)) (Lit (Int i)) , rarg] ← args → App (Instr (GMPOther AddUI)) [Lit (Fin 64 i) , rarg]
    | [larg , Cast (CastInstr (GMPZext _)) (Lit (Int i))] ← args → App (Instr (GMPOther AddUI)) [Lit (Fin 64 i) , larg]
    | _ ← args → App (Instr (GMPInstr i)) args
  IntInstr Sub
    | [Cast (CastInstr (GMPZext _)) (Lit (Int i)) , rarg] ← args → App (Instr (GMPOther UISub)) [Lit (Fin 64 i) , rarg]
    | [larg , Cast (CastInstr (GMPZext _)) (Lit (Int i))] ← args → App (Instr (GMPOther SubUI)) [larg , Lit (Fin 64 i)]
    | _ ← args → App (Instr (GMPInstr i)) args
  IntInstr Mul
    -- ? MulUI
    | [Lit (Fin 64 _i) , _rarg] ← args → App (Instr (GMPOther MulSI)) args
    | [larg , Lit (Fin 64 i)]   ← args → App (Instr (GMPOther MulSI)) [Lit (Fin 64 i) , larg]
  PredInstr LECmp -- TODO other cmp types
    -- CMPAbsD CMPAbsUI
    -- TODO spawn the icmp instruction here
    | [Cast (CastInstr (GMPZext _n)) (Lit (Int i)) , rarg] ← args →
        mkCmpInstr GECmp [App (Instr (GMPOther CMPUI)) [rarg , Lit (Fin 64 i)] , Lit (Fin 32 0)] -- flip the icmp
    | [larg , Cast (CastInstr (GMPZext _n)) (Lit (Int i))] ← args →
        mkCmpInstr LECmp [App (Instr (GMPOther CMPUI)) [larg , Lit (Fin 64 i)] , Lit (Fin 32 0)]
  IntInstr IPow
    -- powmui ?
    | [Lit (Fin 64 _) , Lit (Fin 64 _)] ← args → App (Instr (GMPOther UIPowUI)) args
    | [_larg , Lit (Fin 64 _)]          ← args → App (Instr (GMPOther PowUI)) args
  -- nothing to fold
  i → App (Instr (GMPInstr i)) args
