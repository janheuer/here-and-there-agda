# Formalisation of the Logic of Here-And-There and ASP in Agda
This repository formalises some aspects of the logic of here-and-there and Answer Set Programming (ASP) in [Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php).

## Overview
The formalisation currently encompasses three main topics:

1. Logic programs as a normal form of the logic of here-and-there
2. The connection between the logic of here-and-there and ASP (equilibrium models and strong equivalence)
3. Definition of stable models using the reduct operation

See the module structure below for more details. See the bibliography for references used to develop this formalisation.

## Module Structure
[`Formula`](Formula/Formula.md)
- definition of formulas and theories
- definition of special formulas (i.e. different kinds of logic programs)

[`Classical`](Classical/Classical.md)
- classical interpretations and model relation
- proofs of some tautologies

[`HereAndThere`](HereAndThere/HereAndThere.md)
- here-and-there interpretations and model relation
- proofs of simple properties, equivalences, and tautologies
- equivalence of theories and logic programs

`Equilibrium`
- definition of equilibrium models
- definition of strong equivalence
- ht equivalence implies strong equivalence

`AnswerSet`
- definition of reduct
- definition of answer sets using reducts
- equivalence to equilibrium models

`NatHelper`
- helper theorems on natural numbers

`FunctionHelper`
- some simple helper theorems for type theoretic constructions

## Bibliography
\[CabalarFerraris2007\]
Cabalar, P., & Ferraris, P. (2007). Propositional theories are strongly equivalent to logic programs. Theory and Practice of Logic Programming, 7(6), 745-759. [doi:10.1017/S1471068407003110](https://doi.org/10.1017/S1471068407003110)

\[Ferraris2005\]
Ferraris, P. (2005). Answer Sets for Propositional Theories. Logic Programming and Nonmonotonic Reasoning (Vol. 3662, pp. 119–131). [doi:10.1007/11546207_10](https://doi.org/10.1007/11546207_10)

\[LifschitzEtAl1999\]
Lifschitz, V., Tang, L.R. & Turner, H. (1999). Nested expressions in logic programs. Annals of Mathematics and Artificial Intelligence 25, 369–389. [doi:10.1023/A:1018978005636](https://doi.org/10.1023/A:1018978005636)

\[LifschitzEtAl2001\]
Lifschitz, V., Pearce, D., & Valverde, A. (2001). Strongly equivalent logic programs. ACM Transactions on Computational Logic, 2(4), 526–541. [doi:10.1145/383779.383783](https://doi.org/10.1145/383779.383783)

\[Pearce1997\]
Pearce, D. (1997). A new logical characterisation of stable models and answer sets. Non-Monotonic Extensions of Logic Programming (Vol. 1216, pp. 57–70). [doi:10.1007/BFb0023801](https://doi.org/10.1007/BFb0023801)

## Notes
### Unicode
This formalisation makes use of many Unicode symbols for defining operations/relations using standard notations.
A list of (most) symbols is [available](unicode.md) together with how to write them using the Agda input mode.

### Agda Constructions
The standard library of Agda provides many common type theoretic constructions.
While these constructions are generally well-known their Agda specific syntax may not be as well-known.
Therefore we reproduce their types below for easy reference.
For full details of these constructions check the standard library.

``` agda
[ _ , _ ] : {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
```

``` agda
< _ , _ > : {A B C : Set} → (A → B) → (A → C) → A → B × C
```

``` agda
subst : {A : Set} → (P : A → Set) → {x y : A} → x ≡ y → P x → P y
```

``` agda
map : {A B C D : Set} → (A → C) → (B → D) → A × B → C × D
```

Some other common constructions that are not part of the standard library are included in the module `FunctionHelper`.

## Agda Version
The code is tested on Agda version `2.7.0.1`.
