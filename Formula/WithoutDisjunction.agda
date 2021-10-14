module Formula.WithoutDisjunction where

open import Formula.Base

-- formulas without disjunction ------------------------------------------------
isF\∨ : F → Set
isF\∨ ⊥       = Unit
isF\∨ (V a)   = Unit
isF\∨ (f ∧ g) = (isF\∨ f) × (isF\∨ g)
isF\∨ (f ∨ g) = Ø
isF\∨ (f ⇒ g) = (isF\∨ f) × (isF\∨ g)

record F\∨ : Set where
  constructor f\∨
  field
    f\∨f : F
    f\∨p : isF\∨ f\∨f

open F\∨ public
