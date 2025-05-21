# HereAndThere

`Base`
- here-and-there interpretations
- model relation 
- types for validity and validity of equivalences

TODO `Properties`
- total ht is equivalent to classical logic
- truth in <H,T> implies truth in <T,T>
- negation in ht only depend on there component 
- contradiction (i.e. if `¬f` and `f` hold every formula holds)
- if `¬f` holds, `f ⇒ g` holds for every g
- ht is three valued (and thus decidable)

TODO `Equivalences`
- `⇔` is an equivalence relation 
- equational reasoning for ht equivalences
- commutativity and associativity
- identities and zeroes
- distributivity
- substitution

TODO `Tautologies`
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

TODO `Language`
- restricting interpretations to languages
- increasing restricted language preserves satisfiability
- restriction to language preserves satisfiability

TODO `LogicPrograms`
- equivalence of theories and different kinds of logic programs
- the structure of sub-module is as follows: `LogicProgram.Nested` show equivalence from theories to nested logic programs
- the following sub-module show the equivalence from the previous form of logic programs the form of logic programs that give the name of the sub-module

    `LogicPrograms.Nested`
    - every formula/theory is equivalent to a nested logic program
    - conjunction, disjunction, and implications of nested logic programs is a nested logic program
    - every formula without disjunction is equivalent to a nested logic program
    
    `LogicPrograms.DisjunctiveConjunctive`
    - every nested logic programs is equivalent to a logic program with rules of form dnf `⇒` cnf
    - every nested expression is equivalent to a dnf/cnf
    
    `LogicPrograms.SimpleDisjunctiveConjunctive`
    - every logic program with rules of form dnf `⇒` cnf is equivalent to a logic program with rules of form sc `⇒` sd
    - removal of disjunction in rule bodies
    - removal of conjunction in rule heads
    
    `LogicPrograms.DoubleNegation`
    - every logic program with rules of form sc `⇒` sd is equivalent to a logic program with double negation
    - removal of rules containing `⊤` in head
    - removal of rules containing `⊥` in body
    
    `LogicPrograms.Base`
    - every theory is (strongly) equivalent to a logic program
    - removal of double negation in logic programs containing double negation
    - rewriting of body/head expressions with double negation to extract one double negation 

## Naming & Comment Conventions
In this module if comments mention equivalence this means HT-equivalence unless otherwise specified.
Similarly certain variables are name, e.g., `⊧f` means in general that the variable is a HT proof unless it is the context of a classical proof component.
In context where we have both classical and HT component the variable names and comments will indicate specifically which semantics is meant.
