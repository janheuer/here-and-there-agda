module Classical.Base where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool renaming (Bool to 𝔹) using (true ; false)
open import Data.Empty renaming (⊥ to Ø) using ()
open import Data.Sum.Base using (_⊎_)
open import Data.Product using (_×_)

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
