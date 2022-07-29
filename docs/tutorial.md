An empty Irie file is devoid of bindings, you can `import imports/prelude` to bring some cpu instructions and basic functions into scope. We'll come back to this, but for now let's think of Irie as a theorem proover.

## Label (introduce a sum type):
```
-- optional type alias
Nat = Z | S Nat -- Peano encoded natural numbers

zero : Nat
zero = Z -- If we don't declare nor pattern match on a label, we need to write #Z to show Z is not an out of scope name.
one = S Z -- label a label
two = S (S Z)
```

It's worth noting that Irie will encode Nat as a machine Int, and not a linked list. Generally Irie goes to extreme lengths to optimally encode constructed data.

## Type Annotations
Type annotations are NEVER required, Irie always infers types for itself before checking the validity of any type annotations. However, Type annotations may be more restricive than inferred types (sometimes useful), and Irie will re-use type aliases since they help reduce the printed size of types and are often clearer

```
three : Nat
three = S (S (S Z))
-- Or as inferred: three : µx.[Z | S x]
```
µ introduces a recursive type. Subtyping means these types are equivalent: `µx.[Z | S x] <=> x & [Z | s x]`

## Match (eliminate a sum type):
```
inc Z = S Z
Bool = True | False
isTwo : Nat -> Bool
isTwo = \case
  S (S Z) => True
  _       => False -- '_' matches unconditionally

```
due to the use of '_' the inferred domain for this function is every single label possible, so it's good practice to either not use the unconditional pattern match '_' or give a restricted type annotation.

## Product types
```
-- Optional type alias
Rectangle = { x : Nat , y : Nat }

-- Introduce a product type
rectangle1 : Rectangle
rectangle1 = { x = Z ; y = S Z }

-- Eliminate a product type
getX r = r.x
```
