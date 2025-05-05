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

`Language`
- definition of languages
- language of a formula
- properties of languages

`LogicPrograms`
- definition of different types of logic programs

    `LogicPrograms.Base`
    - definition of logic programs
    - bodies/heads are conjunction/disjunction of atoms and negated atoms

    `LogicPrograms.DoubleNegation`
    - definition of logic programs with double negation 
    - bodies/heads have same structure as in logic programs but double negation is allowed
    
    `LogicPrograms.DisjunctiveConjunctive`
    - definition of simple disjunction/conjunction (sc/sd): disjunctions/conjunction of atom preceded by up to two negations
    - definition of logic programs with with body as simple conjunction and head as simple disjunction
    - definition of disjunctive normal form (dnf): disjunction of simple conjunction (analogous definition of conjunctive normal form (cnf))
    - definition of logic programs with body as dnf and head as cnf
    
    `LogicPrograms.Nested`
    - definition of nested logic programs
    - body and head are nested expressions
    - nested expressions are formulas without `⇒`, but `⊤` and `¬` are allowed
