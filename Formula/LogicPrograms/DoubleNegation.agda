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

record BE2¬ : Set where
  constructor be2¬
  field
    be2¬f : F
    be2¬p : isBE2¬ be2¬f

open BE2¬ public

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

record HE2¬ : Set where
  constructor he2¬
  field
    he2¬f : F
    he2¬p : isHE2¬ he2¬f

open HE2¬ public

-- rules
isR2¬ : F → Set
isR2¬ (b ⇒ h) = (isBE2¬ b) × (isHE2¬ h)
isR2¬ _       = Ø

record R2¬ : Set where
  constructor r2¬
  field
    r2¬f : F
    r2¬p : isR2¬ r2¬f

open R2¬ public

-- logic programs
isLP2¬ : Th → Set
isLP2¬ [] = Unit
isLP2¬ (r ∷ rs) = (isR2¬ r) × (isLP2¬ rs)

record LP2¬ : Set where
  constructor lp2¬
  field
    lp2¬t : Th
    lp2¬p : isLP2¬ lp2¬t

open LP2¬ public
