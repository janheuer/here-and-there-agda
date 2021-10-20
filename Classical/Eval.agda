module Classical.Eval where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_,_)
open import Data.Sum renaming (inj₁ to inl ; inj₂ to inr)
open import Data.Bool renaming (Bool to 𝔹 ; _∧_ to _∧𝔹_ ; _∨_ to _∨𝔹_ ;
                                not to ¬𝔹)

open import Classical.Base
open import BoolHelper

-- alternative model definition ------------------------------------------------
evalC : IPC → F → 𝔹
evalC _ ⊥ = false
evalC i (V a) = i a
evalC i (f ∧ g) = (evalC i f) ∧𝔹 (evalC i g)
evalC i (f ∨ g) = (evalC i f) ∨𝔹 (evalC i g)
evalC i (f ⇒ g) = (evalC i f) ⇒𝔹 (evalC i g)

infix 20 _⊧Ce_

_⊧Ce_ : IPC → F → Set
i ⊧Ce f = evalC i f ≡ true

-- equivalence proof -----------------------------------------------------------
⊧C-to-⊧Ce : {i : IPC} → {f : F} → i ⊧C f → i ⊧Ce f
⊧Ce-to-⊧C : {i : IPC} → {f : F} → i ⊧Ce f → i ⊧C f

⊧C-to-⊧Ce {i} {V a} s = s
⊧C-to-⊧Ce {i} {f ∧ g} (sf , sg) = ×-to-∧𝔹 (⊧C-to-⊧Ce sf , ⊧C-to-⊧Ce sg)
⊧C-to-⊧Ce {i} {f ∨ g} (inl sf) = ⊎-to-∨𝔹 (inl (⊧C-to-⊧Ce sf))
⊧C-to-⊧Ce {i} {f ∨ g} (inr sg) = ⊎-to-∨𝔹 (inr (⊧C-to-⊧Ce sg))
⊧C-to-⊧Ce {i} {f ⇒ g} s = →-to-⇒𝔹 (λ i⊧Cef → ⊧C-to-⊧Ce (s (⊧Ce-to-⊧C i⊧Cef)))

⊧Ce-to-⊧C {i} {V a} s = s
⊧Ce-to-⊧C {i} {f ∧ g} s with ∧𝔹-to-× s
... | (sf , sg) = (⊧Ce-to-⊧C sf , ⊧Ce-to-⊧C sg)
⊧Ce-to-⊧C {i} {f ∨ g} s with ∨𝔹-to-⊎ s
... | inl sf = inl (⊧Ce-to-⊧C sf)
... | inr sg = inr (⊧Ce-to-⊧C sg)
⊧Ce-to-⊧C {i} {f ⇒ g} s = λ i⊧Cf → ⊧Ce-to-⊧C ((⇒𝔹-to-→ s) (⊧C-to-⊧Ce i⊧Cf))
