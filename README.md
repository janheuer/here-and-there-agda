This repository implements parts of the paper
[Cabalar, P., & Ferraris, P. (2007). Propositional theories are strongly equivalent to logic programs. Theory and Practice of Logic Programming, 7(6), 745-759. doi:10.1017/S1471068407003110](https://www.cambridge.org/core/product/identifier/S1471068407003110/type/journal_article)

# Structure
`Formula.agda`
- definition of formulas and theories

`LogicPrograms.agda`
- definition of logic programs

`BoolHelper.agda`
- helper functions for dealing with booleans (for model relations based on `eval`)

`Classical.agda`
- classical interpretations and model relation
- alternative model relation based on `eval` (and equivalence proof)
- law of excluded middle

`HereAndThere.agda`
- imports `HereAndThere/{Base,Properties,Equivalences,Tautologies}.agda` publicly

    `HereAndThere/Base.agda`
    - here-and-there interpretations and model relation
    
    `HereAndThere/Properties.agda`
    - total here-and-there is classical logic
    - truth here implies truth there
    - negation only depends on there
    
    `HereAndThere/Equivalences.agda`
    - <=> is an equivalence relation
    - simple properties of implications, conjunction, and disjunction (i.e. identity, replacement, commutativity, associativity)
    - properties of disjunction and implication (currying, distributivity)
    
    `HereAndThere/Tautologies.agda`
    - weak lem, hosoi, demorgan
    - removal of disjunction, nested implication
    
    `HereAndThere/LogicPrograms.agda`
    - every theory is equivalent to a nested logic program
    
    `HereAndThere/Eval.agda`
    - alternative model relation based on `eval`
    - equivalence proof
    - alternative implementation of some properties
