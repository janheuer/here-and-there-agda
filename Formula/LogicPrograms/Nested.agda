module Formula.LogicPrograms.Nested where

-- nested logic programs have rules of the form
-- body ⇒ head
-- where body and head are nested expressions
-- a nested expression is a formula that does not contain implication
-- unless it is a negation (i.e. an implication of the form f ⇒ ⊥)

open import Agda.Builtin.Unit renaming (⊤ to Unit) using ()
open import Data.Empty renaming (⊥ to Ø) using ()
open import Data.Product using (_×_ ; Σ-syntax)
                         renaming (proj₁ to p1)
open import Data.List using (List ; [] ; _∷_)

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
