# Codegen

# Data
## Problem
How to handle Labels and Matches ? On the surface, labels package memory which is then copied around up and down the call stack until they are split by a Match.
* Heap memory is expensive:
  - chunk headers, linked lists of free chunks, sorting chunks, fn call overhead etc..
  - the heap becomes increasingly fragmented, which is difficult to come back from
  - Stack Memory causes far fewer CPU cache misses (which tend to cost around 100 ticks)
* memory must be freed once unneeded
* Data is sometimes shared - but copying is expensive
* Multithreaded (even distributed networks and GPUs) environment
* support dropping fields / labels (via subtyping). `eg. {x;y} is a valid {x}`
* support inplaceing of linear data

## Stack Machine
* Memory can only ever be passed down
* we cannot return data of unkown size ; but we can pass down function pointers to tail-call
* SplitTree = { [ freeVars ] ; [ || rec | SplitTree | fnPtr || ] }

### By relative Stack position:
 - label > ST => pass the label down
 - ST > label => pass the ST down
 - ST ST > label*2 => sync labels for ST eval ?
 - label*2   > ST => ez
 - generator > ST*2 => pass gen down and eval both ST's at same time (?)
 - ST > label > ST  => pass ST down & pass label down

### By StackFrame:
  1. if returning data, take extra splitTree argument
  2. Label: write locally ; maybe passdown
  3. Match: if splitting a function call; give it a splitTree. else execute directly

## Examples:
```haskell
-- Parallel splits
zip a b = case a of
  [] => []
  x : xs => case b of
    [] => []
    y : ys => (x,y) : zip xs ys

reverse l = let
  rev []     a = a
  rev (x:xs) a = rev xs (x:a)
in rev l []

eg. recursive split = \case
  []   -> 0
  x:xs -> 1 + len xs

eg. mulitisplit = case A of
  x => case B of y => ..
  _ => case C of z => ..
```

## Lexicon
 * Con          = single label
 * Gen          = recursive label
 * PAp          = partial application (free variables and a function pointer)
 * Dropped      = ignored via subtyping (eg. `{a:A} <: {}` ; `[| b:B |] <: [| |]`)
 * Polymorphism = Data of variable type (and size)
 * Linear       = Data is consumed once (the memory is inplaceable)
 * OnSplit      = Function called on record (@indexes) or sum-data @(@indexes)
 * Split Tree   = List(1 per shared Split) of Lists(sum-alts) of Splitters

# Streaming
* Distribute       = share streams
* zipWith          = combine streams
* Map              = modify streams
* Folds            = Reduce streams
* Buffer           = eg. reverse / array etc..
* Yield = Callback for 1 elem ?!

```haskell
SplitTree = | STCont Fn | STAlts [Fns]
evalSplitTree
yieldST

Stream =
 | Generator  -- basic stream
 | Map Fn Stream
 | Buffer (n:Int)

 -- duplicate streams
 | Tee
 -- merge streams (phi node ?)
 | Zip (2 X ST)

 | Array      -- index function available
```

? need access to Stack frame
