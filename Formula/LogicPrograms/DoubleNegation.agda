module Formula.LogicPrograms.DoubleNegation where

open import Formula

-- definition of logic programs with double negation ---------------------------
-- body expressions
isBE2¬ : F → Set
-- empty conjunction
isBE2¬ (⊥ ⇒ ⊥)     = Unit
-- literals
isBE2¬ (V a)       = Unit
isBE2¬ ((V a) ⇒ ⊥) = Unit
isBE2¬ (((V a) ⇒ ⊥) ⇒ ⊥) = Unit
-- conjunction of BE
isBE2¬ (f ∧ g)     = (isBE2¬ f) × (isBE2¬ g)
isBE2¬ ⊥           = Ø
isBE2¬ (f ∨ g)     = Ø
isBE2¬ (f ⇒ g)     = Ø

BE2¬ : Set
BE2¬ = Σ[ f ∈ F ] (isBE2¬ f)

-- head expressions
isHE2¬ : F → Set
-- empty disjunction
isHE2¬ ⊥           = Unit
-- literals
isHE2¬ (V a)       = Unit
isHE2¬ ((V a) ⇒ ⊥) = Unit
isHE2¬ (((V a) ⇒ ⊥) ⇒ ⊥) = Unit
-- disjunction of HE
isHE2¬ (f ∨ g)     = (isHE2¬ f) × (isHE2¬ g)
isHE2¬ (f ∧ g)     = Ø
isHE2¬ (f ⇒ g)     = Ø

HE2¬ : Set
HE2¬ = Σ[ f ∈ F ] (isHE2¬ f)

-- rules
isR2¬ : F → Set
isR2¬ (b ⇒ h) = (isBE2¬ b) × (isHE2¬ h)
isR2¬ _       = Ø

R2¬ : Set
R2¬ = Σ[ f ∈ F ] (isR2¬ f)

-- logic programs
isLP2¬ : Th → Set
isLP2¬ [] = Unit
isLP2¬ (r ∷ rs) = (isR2¬ r) × (isLP2¬ rs)

LP2¬ : Set
LP2¬ = Σ[ t ∈ Th ] (isLP2¬ t)
