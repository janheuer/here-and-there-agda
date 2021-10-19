module Formula.LogicPrograms.Nested where

open import Formula

-- definition of nested logic programs -----------------------------------------
-- nested expressions
-- i.e. formulas without ⇒, but ⊤ and ¬ allowed
isNE : F → Set
isNE ⊥       = Unit
isNE (V a)   = Unit
isNE (f ∧ g) = (isNE f) × (isNE g)
isNE (f ∨ g) = (isNE f) × (isNE g)
isNE (f ⇒ ⊥) = isNE f
isNE (f ⇒ g) = Ø

NE : Set
NE = Σ[ f ∈ F ] (isNE f)

-- nested rules
-- i.e. rules where head and body are nested expressions
isNR : F → Set
isNR (f ⇒ g) = (isNE f) × (isNE g)
isNR _       = Ø

NR : Set
NR = Σ[ f ∈ F ] (isNR f)

-- nested logic programs
isNLP : Th → Set
isNLP []       = Unit
isNLP (r ∷ rs) = (isNR r) × (isNLP rs)

NLP : Set
NLP = Σ[ t ∈ Th ] (isNLP t)

NLP2F : NLP → F
NLP2F Π = Th2F (p1 Π)
