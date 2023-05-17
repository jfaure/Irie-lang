First class polymorphism:
\i => if (i i) true then true else true
i used as:
i : (i1 -> i1) -> (i1 -> i1)
i : i1 -> i1
=> Need to consider i may be polymorphic
i : a -> a

inferred type: a & (a -> i1 -> i1) -> i1
contravariant recursive type; this only makes sense if a is higher rank polymorphic:
a & (a -> i1 -> i1) => (Π B -> B -> B)
