# Formula

`Base`
- definition of variables
- definition of formulas
- formula abbreviations

`Theories`
- definition of theories
- conversion of theories to formulas
- element operator for theories

`Decidable`
- equality on formulas is decidable

`Substitution`
- substitution in formulas

`WithoutDisjunction`
- type for formulas that do not contain disjunction

`LogicPrograms`
- definition of different types of logic programs

    `LogicPrograms.Base`
    - definition of logic programs
    - bodies/heads are conjunction/disjunction of atoms and negated atoms

    `LogicPrograms.Double Negation`
    - definition of logic programs with double negation 
    - bodies/heads have same structure as in logic programs but double negation is allowed
    
    `LogicPrograms.Nested`
    - definition of nested logic programs
    - body and head are nested expressions
    - nested expressions are formulas without `⇒`, but `⊤` and `¬` are allowed
