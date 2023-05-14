# Fast (output programs)
## Fusion
* Eliminates need for intermediate memory
## β-optimal
* All shareable computations are shared (even inside partial function applications)
* Efficient memory management via dup nodes
* lazy clone instead of copying, faster and avoids uneccessary work
## Subtyping
* More precise types means more precise memory management
* enables auto SIMD (instruction parallelisation)

# Fast (compilation speed)
## Small compiler (<6000 lines)
## Internal coherence

# Fast (development time)
## Subtyping
* Permits simpler efficient algorithms
* Better libraries handling fusion and correcting historic mistakes

# Safe (Programs don't crash due to type mismatches or memory mismanagement)
## Subtyping
* All function arguments are guaranteed to subtype their expected type
## Dependent types
* Fully expressive types allows to guarantee any condtions at compiletime

# Easy
## Subtyping
* type annotations aren't required
* subtypes are more precise then predeclared ones
