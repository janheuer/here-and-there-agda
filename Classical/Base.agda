module Classical.Base where

open import Agda.Builtin.Equality using (_≡_ ; refl) public
open import Data.Bool renaming (Bool to 𝔹) hiding (_∧_ ; _∨_) public
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim) public
open import Data.Sum.Base using (_⊎_ ; [_,_])
                          renaming (inj₁ to inl ; inj₂ to inr) public
open import Data.Product using (_×_ ; _,_)
                         renaming (proj₁ to p1 ; proj₂ to p2) public

open import Formula public

-- classical interpretations ---------------------------------------------------
IPC : Set
IPC = Var → 𝔹

-- satisfiability of formulas in classical logic -------------------------------
_⊧C_ : IPC → F → Set
i ⊧C ⊥ = Ø
i ⊧C (V a) = i a ≡ true
i ⊧C (f ∧ g) = (i ⊧C f) × (i ⊧C g)
i ⊧C (f ∨ g) = (i ⊧C f) ⊎ (i ⊧C g)
i ⊧C (f ⇒ g) = (i ⊧C f) → (i ⊧C g)

ValidC : F → Set
ValidC f = (i : IPC) → i ⊧C f
