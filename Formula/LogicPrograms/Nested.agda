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

record NE : Set where
  constructor ne
  field
    nef : F
    nep : isNE nef

open NE public

-- nested rules
-- i.e. rules where head and body are nested expressions
isNR : F → Set
isNR (f ⇒ g) = (isNE f) × (isNE g)
isNR _       = Ø

record NR : Set where
  constructor nr
  field
    nrf : F
    nrp : isNR nrf

open NR public

-- nested logic programs
isNLP : Th → Set
isNLP []       = Unit
isNLP (r ∷ rs) = (isNR r) × (isNLP rs)

record NLP : Set where
  constructor nlp
  field
    nlpt : Th
    nlpp : isNLP nlpt

open NLP public
