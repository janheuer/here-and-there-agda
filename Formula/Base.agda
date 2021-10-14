module Formula.Base where

open import Agda.Builtin.Equality using (_≡_ ; refl) public
open import Agda.Builtin.Unit using (tt) renaming (⊤ to Unit) public
open import Data.Nat using (ℕ) public
open import Data.List using (List ; _∷_ ; []) public
open import Data.Empty renaming (⊥ to Ø) public
open import Data.Sum using (_⊎_) public
open import Data.Product using (_×_) public

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
