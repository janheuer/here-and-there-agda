module Formula where

open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Agda.Builtin.Unit using (tt) renaming (⊤ to Unit)
open import Data.Nat using (ℕ)
open import Data.List using (List ; _∷_ ; [])
open import Data.Empty renaming (⊥ to Ø)
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_)

-- propositional signature -----------------------------------------------------
data Var : Set where
  X : ℕ → Var

-- formulas --------------------------------------------------------------------
infixr 12 _⇒_
infixr 10 _∧_
infixr  8 _∨_

data F : Set where
  ⊥   : F
  V   : Var → F
  _∧_ : F → F → F
  _∨_ : F → F → F
  _⇒_ : F → F → F

-- formula abbreviations
¬ : F → F
¬ f = f ⇒ ⊥

⊤ : F
⊤ = ⊥ ⇒ ⊥

_⇔_ : F → F → F
f ⇔ g = (f ⇒ g) ∧ (g ⇒ f)

-- theories --------------------------------------------------------------------
Th : Set
Th = List F

-- theory as formula
Th2F : Th → F
Th2F []       = ⊤
Th2F (f ∷ th) = f ∧ (Th2F th)

-- element operator for theories
infix 15 _∈_

_∈_ : F → Th → Set
f ∈ [] = Ø
f ∈ (g ∷ gs) = (f ≡ g) ⊎ (f ∈ gs)

All : (F → Set) → Th → Set
All P th = (f : F) → f ∈ th → P f

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
