module Formula.Base where

open import Data.Nat using (ℕ)

-- propositional signature -----------------------------------------------------
-- propositional variables are indexed by natural numbers
-- thus we have an infinite vocabulary
data Var : Set where
  X : ℕ → Var

-- formulas --------------------------------------------------------------------
infixr 12 _⇒_
infixr 10 _∧_
infixr  8 _∨_

data F : Set where
  -- 1) atomic cases
  -- falsity
  ⊥   : F
  -- propositional variables/atoms
  V   : Var → F
  -- 2) recursive cases
  -- formulas can be combined with ...
  -- conjunction
  _∧_ : F → F → F
  -- disjunction
  _∨_ : F → F → F
  -- implication
  _⇒_ : F → F → F

-- formula abbreviations
-- negation
¬ : F → F
¬ f = f ⇒ ⊥

-- truth
⊤ : F
⊤ = ⊥ ⇒ ⊥

--equivalence
_⇔_ : F → F → F
f ⇔ g = (f ⇒ g) ∧ (g ⇒ f)
