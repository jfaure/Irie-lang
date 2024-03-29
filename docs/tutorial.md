# Tutorial
An empty Irie file is devoid of bindings, you can `import imports/prelude` to bring cpu instructions and basic functions into scope. We'll look at the contents of prelude later, but for now let's think of Irie as a theorem proover. There are only 3 type constructors, each with a corresponding term level syntax for construction and elimination
* `->` function type `_+_ : Int -> Int -> Int`
* `[]` sum type `Maybe A = [Just A | Nothing]`
* `{}` product type `rectangle : { x : Int , y : Int }`

## Type Annotations
Type annotations are NEVER required, Irie always infers types for itself before checking the validity of any type annotations. Still, explicit annotations are useful:
1. Documentation: Type signatures supplement function definitions.
2. Clarity: Type aliases propagate and tend to reduce the printed size of types.
3. Restricting to a subtype of the (often too general) inferred type. eg. the inferred type for matching unconditionally: `_ => something` matches every single label possible

## Functions
Eg. `f x y = x y` Here we see abstraction (introduce a function `f x y =` taking 2 args x and y), and application (eliminate a function by giving it an argument(s) `x y` function x called with y as argument)

The semantics for application is β-reduction: All uses of a functions argument as defined in its abstraction are replaced by the argument given to it. Thus `test = f inc 1` is `inc 1`

## Sum type: Label and Match
### Label
```
-- optional type alias
Nat = Z | S Nat -- Peano encoded natural numbers

zero : Nat
zero = Z -- If we don't declare nor pattern match on a label, we need to write #Z to show Z is not an out of scope name.
one = S Z -- label a label
two = S (S Z)
```

It's worth noting that Irie will encode Nat as a machine Int, and not a linked list. Generally Irie goes to extreme lengths to optimally encode constructed data.

```
three : Nat
three = S (S (S Z))
-- Or as inferred: three : µx.[Z | S x]
```

µ introduces a recursive type. Subtyping means these types are equivalent: `µx.[Z | S x] <=> x & [Z | s x]`

### Match (eliminate a sum type):

```
inc Z = S Z
Bool = True | False
isTwo : Nat -> Bool
isTwo = \case
  S (S Z) => True
  _       => False -- '_' matches unconditionally

```

due to the use of '_' the inferred domain for this function is every single label imaginable, so it's good practice to either not use the unconditional pattern match '_' or give a restricted type annotation.

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
