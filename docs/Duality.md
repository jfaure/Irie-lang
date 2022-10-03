# Duality

* Function Inputs vs outputs (also Data vs Computation)
* Monad (wrapped focus) vs Comonad (unwrapped focus)
* Sage vs sceptic (one constructs proofs, the other refutes theories)

we can also think of conjunction as a negative type.
* + pair = pair construction (give me two values, that's a pair)
* - pair = suspended computation that awaits you asking it for its first or second component.

Because functions and records are negative types it's natural to pass functions as arguments to records
