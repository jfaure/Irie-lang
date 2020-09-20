# Top level
Identifiers may freely mix alphanumerical characters and symbols,
they are space (or reserved character) separated
Modules are first class dependent records, ie. a list of assignments
```haskell
reservedChars = "\"@.(){};\\" -- as defined in the parser itself
f = 3
add a b = a + b -- normal function
add2 = \a b => add a b -- '\' introduces an anonymous function
```

# Mixfix expressions
You can define arbitrary pieces of syntax, using '_' to indicate where arguments go.
This allows you to redefine vast quantities of syntax, simply by eg. `import C`
```haskell
[_] = \i => i --the identity function, resulting in usual parentheses behavior
_+2 = \a => a + 2
_addMixFix_ = add2 -- `eg = 2 addMixFix 3`
```

# Terms and Types
All terms (and types) have a type, which gives as much compile-time information about it's term as you please.
terms and types are syntactically equivalent (they can be manipulated in the same ways)

There exists successive universes of types, and given (t : ty); ty resides in a higher universe.
```haskell
((5 : Int) : Set) : Set2 -- etc..
1 , 2 , 3 : Vec 3 Int    -- a dependent type, indexed by the length of the vector
```

# Terms
There are very few syntactic constructions
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

# Effects
Both observable and non-observable effects are a part of the type-theory, since they provide crucial information for both the programmer and the compiler, since the source language is otherwise completely pure.

```haskell
IO = || In | Out || -- IO is the effect type of the main function

-- the print syscall writes a string to stdout
-- it returns an Int in the Out effect
print  : String -> Int % Out
readLn : String % In -- readLn reads a line from stdin

main : IO ()
  = print "hello" -- notice that Out is a subtype of IO
```

# Dependent types
We are interested in dependent types first and foremost because they supplement basic types
with useful information.
```haskell
2 , 5 : Vec 2 Int -- here the size of the list is constant (also doesn't exist at runtime)
_,_ :: {n:Int} : A -> Vec n A -> Vec (n + 1) A -- _,_ prepends an element, incrementing the vec size
```

# Types as propositions
Mathematically speaking, a dependent type is given by `Π(x : A) T(x)`
this means the type T depends on x, which is in it's scope because of the pi-binder

Types can be viewed as propositions, and their terms a proof of that proposition
```Haskell
3 : Int -- the 'proposition' Int is trivially proven by supplying an inhabitant

-- 3 being equal to 3 is known as definitional equality
-- propositional equality includes non-trivial cases
..
```
