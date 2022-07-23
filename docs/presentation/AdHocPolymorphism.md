```haskell
-- Num typeclass:
neg : Π A → A & { Num : [ gmp | prim ] , ret : GMPInt & PrimInt } → A
neg a = case a.Num of
  gmp  a -> GMP.neg  a.ret
  prim a -> PRIM.neg a.ret

-- many typeclasses:
-- Label contents are duplicated, but codegen is free to merge them
Π A → A & { v -> Num : [ gmp gmpValue | prim primValue ] , EQ : [ gmp gmpValue | prim primValue }

```
