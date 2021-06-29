This repository implements parts of the paper
[Cabalar, P., & Ferraris, P. (2007). Propositional theories are strongly equivalent to logic programs. Theory and Practice of Logic Programming, 7(6), 745-759. doi:10.1017/S1471068407003110](https://www.cambridge.org/core/product/identifier/S1471068407003110/type/journal_article)

# Structure
`Formula.agda` definition of formulas (and formula abbreviations) and theories

`BoolHelper.agda` several helper functions for dealing with booleans (mostly for model relations based on eval)

For both classical logic and the logic of here-and-there two possible model relations are implemented as well as proof showing that the relations are equivalent.
The relations not based on an `eval` function are the main relations used (for the `eval` relation only a few proofs are implemented).

`Classical.agda`
- classical interpretations
- model relation
- law of excluded middle

`HereAndThere.agda`
- here-and-there interpretations
- model relation
- proofs of properties in section 2.1

`HereAndThereEval.agda`
- alternative model relation based on `eval`
- alternative implementation of some proof of section 2.1
