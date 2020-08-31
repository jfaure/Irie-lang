# Codegen

# Data
## Problem
How to handle Labels and Matches ? Naively, labels package memory which is then copied around up and down the call stack until they are split by a Match.
* Ideally use only stack memory, because heap memory is expensive:
  - bookkeeping (eg. malloc uses headers, linked lists of free chunks, fn call overhead etc..)
  - long-term, the heap fragments, which is very difficult to come back from
* memory must be freed once unneeded
* Data is sometimes shared - but copying is expensive
* Multithreaded (even distributed networks and GPUs) environment
* support dropping fields / labels (via subtyping). `eg. {x;y} is a valid {x}`
* support inplaceing of linear data

## Lexicon
 * Con          = single label
 * Gen          = recursive label
 * PAp          = partial application (free variables and a function pointer)
 * Dropped      = ignored via subtyping (eg. `{a:A} <: {}` ; `[| b:B |] <: [| |]`)
 * Polymorphism = Data of variable type (and size)
 * Linear       = Data is consumed once
 * inplace      = write directly to memory
 * OnSplit      = Function called on record (@indexes) or sum-data @(@indexes)
 * Split Tree   = List(1 per shared Split) of Lists(sum-alts) of Splitters

## Plan
* Memory can only ever be passed down; ie. data of unkown size can never be returned
* SplitTree = { [ freeVars ] ; [ || rec | SplitTree | fnPtr || ] }

By relative Stack position:
  - label > ST => pass the label down
  - ST > label => pass the ST down
  - ST ST > label*2 => sync labels for ST eval ?
  - label*2   > ST => ez
  - generator > ST*2 => pass gen down and eval both ST's at same time (?)
  - ST > label > ST  => pass ST down & pass label down

By StackFrame:
  1. if returning data, take extra splitTree argument
  2. Label: write locally ; maybe passdown
  3. Match: if splitting a function call; give it a splitTree. else execute directly

Primitives
* tailSplit  : SplitTree -> Label -> Val
    tail call upstack splitTree
* doLabel    : Label
    write to local memory
* mkSplit = upstack label ?
  - splitEager : Label -> Match -> Val
  - mkTree     : Maybe SplitTree -> Match -> SplitTree
      package a tree for passdown (using tailTree)

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
