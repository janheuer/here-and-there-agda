module Formula.Base where

open import Data.Nat using (ℕ)

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
