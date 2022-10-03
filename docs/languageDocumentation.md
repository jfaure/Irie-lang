Note. this requires expansion (last updated: August 2021)
# Top level
An Irie file is a dependent record (A list of bindings). It's "module signature" is the type of this record. Records contain assignments and mixfix definitions

# Functions
* Anonymous functions (lambdas) are introduced with \ (also λ) eg. `_+_ = \a b => add a b`
* Named functions: `f x = x + x` `add x = let y = x + x in y`

# Records
A List of bindings with optional type annotations.

Identifiers may freely mix alphanumerical characters and symbols.
```haskell
reservedChars = "\"@.(){};\\" -- as defined in the parser itself
f = 3

callEG = fn arg1 arg2 -- Call a function
add a b = a + b -- define a function
add2    = \a b => add a b -- '\' introduces an anonymous function
```

# Mixfix expressions
You can define new operators, using '_' to indicate where arguments go.
This allows you to redefine vast quantities of syntax, simply by importing mixfixes.
```haskell
[_] = \i => i --the identity function, resulting in usual parentheses behavior: eg = [ 5 ]
_+2 = \a => a + 2  -- eg = 5 +2
_addMixFix_ = add2 -- eg = 2 addMixFix 3
```

# Terms and Types
All terms (and types) have a type, which loosely speaking describes a set of values.
terms and types are syntactically equivalent (they can be manipulated in the same ways)

There exists successive universes of types, and given (t : ty); ty resides in a higher universe.
```haskell
5 : Int : Set : Set2 -- etc..
1 , 2 , 3 : Vec 3 Int    -- a dependent type, indexed by the length of the vector
```

# Terms
There are 3 type constructors, and their corresponding term constructs:
* Functions: Abstraction `\a => a` and application `a b`
* Records:   Construction `{ x = 3 , y = 4 }` and Lens `r.x` `r.x.over (_+_ 1)`
* Sum data:  Label `Cons a b` and Match `\case { Cons a b => a + b }`

```haskell
string = "morning"
i32-8    = 8 : I32    -- a 32 bit number
bigInt-8 = 8 : BigInt -- an arbitrary precision int, uses GMP internally

-- product and sum types
tuple  = 5 ; "afternoon" -- anonymous record
record = { n=3 ; str="evening" }

sumData = -- the categorical dual to a product type
  | Rectangle : { x : Float ; y : Float } -> Shape
  | Circle -> Float -> Shape

-- \case is a builtin function.
-- it's input type is a sum type, and
-- return type is a join (in the subtyping lattice) of the types of its alts
shapeArea : Shape -> Float
 = \case
  | Rectangle { x ; y } => x * y
  | Circle r => π * r ^ 2
```

# Subtyping
A few subtyping relations are builtin, which are very good at obviating the need to be excessively specific
```haskell
f : { x : Int } -> Int      -- f expects as argument a record with a label x of type Int
out = f { x=4 ; y="noise" } -- but will accept any subtype of {x:Int}

-- handle flag handles sumtypes with 2 alts
handleFlag : || Flag1 | Flag2 || -> Int
handleFlag = \case
  | Flag1 => 3
  | Flag2 => 9

oneFlag = Flag1 : || Flag1 ||
ok = handleFlag oneFlag -- || Flag1 || is a subtype of || Flag1 | Flag2 ||

-- Thus one reason for sum types being the mathematical dual of product types is clear

```
# Dependent types
The first point of interest is that dependent types increase the expressivity of our types:
```haskell
2 , 5 : Vec 2 Int -- here the size of the list is constant (also doesn't exist at runtime)
_,_ :: {n:Int} : A -> Vec n A -> Vec (n + 1) A -- _,_ prepends an element, incrementing the vec size
```

# Types as propositions
A dependent type is introduced by `Π(x : A) T(x)`
this means the type T depends on x, which is in it's scope because of the pi-binder

Types can be viewed as propositions, and their terms a proof of that proposition
```Haskell
3 : Int -- the 'proposition' Int is trivially proven by supplying an inhabitant

-- 3 being equal to 3 is known as definitional equality
-- propositional equality includes non-trivial cases
..
```
