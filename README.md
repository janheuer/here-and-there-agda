This repository implements the logic of here-and-there as the logical foundations of Answer Set Programming (ASP).

The current implementation aims to prove that logic programs provide a normal form for arbitrary theories in the logic of here-and-there.
To do so parts of the following two papers are implemented:

\[CabalarFerraris2007\]
Cabalar, P., & Ferraris, P. (2007). Propositional theories are strongly equivalent to logic programs. Theory and Practice of Logic Programming, 7(6), 745-759. [doi:10.1017/S1471068407003110](https://doi.org/10.1017/S1471068407003110)

\[LifschitzEtAl1999\]
Lifschitz, V., Tang, L.R. & Turner, H. (1999). Nested expressions in logic programs. Annals of Mathematics and Artificial Intelligence 25, 369–389. [doi:10.1023/A:1018978005636](https://doi.org/10.1023/A:1018978005636)

# Module Structure
[`Formula`](Formula/Formula.md)
- definition of formulas and theories
- definition of special formulas (i.e. different kinds of logic programs)

[`Classical`](Classical/Classical.md)
- classical interpretations and model relation
- proof of some tautologies

[`HereAndThere`](HereAndThere/HereAndThere.md)
- here-and-there interpretations and model relation
- proofs of simple properties, equivalences, and tautologies
- equivalence of theories and nested logic programs

`NatHelper`
- helper theorems on natural numbers

`BoolHelper`
- helper functions for dealing with booleans (for model relations based on `eval`)
