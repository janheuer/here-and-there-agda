This repository implements parts of the paper
[Cabalar, P., & Ferraris, P. (2007). Propositional theories are strongly equivalent to logic programs. Theory and Practice of Logic Programming, 7(6), 745-759. doi:10.1017/S1471068407003110](https://www.cambridge.org/core/product/identifier/S1471068407003110/type/journal_article)

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
