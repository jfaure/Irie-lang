# case-case notes:
case-case: push/copy outer case to each branch, then the inner case output fuses with outer case labels
Scrut is pre β-reduced , fuse then β-reduce branches and d (after fusion = a single one)
TODO (?) need to inc args within the pushed case (normally case-Abs are distinct, but now we're stacking them)

case (\p1..p2 -> scrut) of branches
=> \p1..p2 -> case scrut of branches
TODO this bruijnAbs applies to the scrut but NOT the branches/d !
| make a new fn that separate scrut/branches (not possible with current syntax)
| New syntax: case-branches to separate scrut from branches and allow \p1..pn S -> pass in branches
| force increment all bruijns in branches (complicated when meeting more bruijnAbs)
| Wrap (blocks pattern matching and too weird)
| Rewrite case-case to resolve all without returning (inner case usually scruts an arg so irreducable)
| Leave the fn in the scrut (Then need to partition trailingArgs to scrut and to branch output)
| case-branches are let-binds (ie. have explicit captures)
