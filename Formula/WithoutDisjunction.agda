module Formula.WithoutDisjunction where

-- this module defines a sublanguage of formulas:
-- formulas that do not contain disjunctions

open import Agda.Builtin.Unit renaming (⊤ to Unit) using ()
open import Data.Empty renaming (⊥ to Ø) using ()
open import Data.Product using (_×_ ; Σ-syntax)

open import Formula.Base

-- formulas without disjunction ------------------------------------------------
isF\∨ : F → Set
isF\∨ ⊥       = Unit
isF\∨ (V a)   = Unit
isF\∨ (f ∧ g) = (isF\∨ f) × (isF\∨ g)
isF\∨ (f ∨ g) = Ø
isF\∨ (f ⇒ g) = (isF\∨ f) × (isF\∨ g)

F\∨ : Set
F\∨ = Σ[ f ∈ F ] (isF\∨ f)
