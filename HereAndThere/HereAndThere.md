# HereAndThere

`Base`
- here-and-there interpretations
- model relation 
- types for validity and validity of equivalences
- two extensions of the model relation to theories (and proof of their equivalence)

`Eval`
- alternative definition of the model relation based on an `eval` function mapping interpretations and formulas to booleans
- equivalence proof of both model relation
- proofs of some ht properties using the `eval` based relation

`Properties`
- total ht is equivalent to classical logic
- truth in <H,T> implies truth in <T,T>
- negation in ht only depend on there component 
- contradiction (i.e. if `¬f` and `f` hold every formula holds)
- if `¬f` holds, `f ⇒ g` holds for every g
- ht is three valued

`Equivalences`
- `⇔` is an equivalence relation 
- equational reasoning for ht equivalences
- commutativity and associativity
- identities and zeroes
- distributivity
- substitution

`Tautologies`
- weak law of excluded middle
- hosoi
- removal of triple negation
- currying
- combining of implications
- reordering of implications
- de-morgan 
- removal of disjunction
- removal of nested implication 
- removal of double negation in implications

`LogicPrograms`
- equivalence of theories and different kinds of logic programs

    `LogicPrograms.Netsed`
    - conjunction, disjunction, and implications of nested logic programs is a nested logic program
    - every formula without disjunction is equivalent to a nested logic program
    - every formula/theory is equivalent to a nested logic program
    
    `LogicPrograms.DoubleNegation`
    - rewriting of body/head expressions with double negation to extract one double negation 
    - removal of double negation in rules containing double negation 
    - removal of double negation in logic programs containing double negation
