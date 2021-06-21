module Classical where

open import Agda.Builtin.Equality
open import Data.Bool renaming (Bool to 𝔹 ; _∧_ to _∧𝔹_ ; _∨_ to _∨𝔹_ ; not to ¬𝔹)
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim)
open import Data.Sum.Base using (_⊎_ ; [_,_]) renaming (inj₁ to inl ; inj₂ to inr)
open import Data.Product using (_×_ ; _,_) renaming (proj₁ to p1 ; proj₂ to p2)

open import BoolHelper
open import Formula

-- classical interpretations ---------------------------------------------------
IPC : Set
IPC = Var → 𝔹

-- satisfiability of formulas in classical logic -------------------------------
evalC : IPC → F → 𝔹
evalC _ ⊥ = false
evalC i (V a) = i a
evalC i (f ∧ g) = (evalC i f) ∧𝔹 (evalC i g)
evalC i (f ∨ g) = (evalC i f) ∨𝔹 (evalC i g)
evalC i (f ⇒ g) = (evalC i f) ⇒𝔹 (evalC i g)

infix 20 _⊧Ce_

_⊧Ce_ : IPC → F → Set
i ⊧Ce f = evalC i f ≡ true

-- alternative model definition ------------------------------------------------
_⊧C_ : IPC → F → Set
i ⊧C ⊥ = Ø
i ⊧C (V a) = i a ≡ true
i ⊧C (f ∧ g) = (i ⊧C f) × (i ⊧C g)
i ⊧C (f ∨ g) = (i ⊧C f) ⊎ (i ⊧C g)
i ⊧C (f ⇒ g) = (i ⊧C f) → (i ⊧C g)

-- equivalence proof
⊧C-to-⊧Ce : {i : IPC} → {f : F} → i ⊧C f → i ⊧Ce f
⊧Ce-to-⊧C : {i : IPC} → {f : F} → i ⊧Ce f → i ⊧C f

⊧C-to-⊧Ce {i} {V a} s = s
⊧C-to-⊧Ce {i} {f ∧ g} (sf , sg) = ×-to-∧𝔹 (⊧C-to-⊧Ce sf , ⊧C-to-⊧Ce sg)
⊧C-to-⊧Ce {i} {f ∨ g} (inl sf) = ⊎-to-∨𝔹 (inl (⊧C-to-⊧Ce sf))
⊧C-to-⊧Ce {i} {f ∨ g} (inr sg) = ⊎-to-∨𝔹 (inr (⊧C-to-⊧Ce sg))
⊧C-to-⊧Ce {i} {f ⇒ g} s = →-to-⇒𝔹 (λ sef → ⊧C-to-⊧Ce (s (⊧Ce-to-⊧C sef)))

⊧Ce-to-⊧C {i} {V a} s = s
⊧Ce-to-⊧C {i} {f ∧ g} s =
  let
    (sf , sg) = ∧𝔹-to-× s
  in
    (⊧Ce-to-⊧C sf , ⊧Ce-to-⊧C sg)
⊧Ce-to-⊧C {i} {f ∨ g} s with ∨𝔹-to-⊎ s
... | inl sf = inl (⊧Ce-to-⊧C sf)
... | inr sg = inr (⊧Ce-to-⊧C sg)
⊧Ce-to-⊧C {i} {f ⇒ g} s = λ x → ⊧Ce-to-⊧C ((⇒𝔹-to-→ s) (⊧C-to-⊧Ce x))

-- f ∨ ¬f
lem : (f : F) → (i : IPC) → i ⊧C (f ∨ (¬ f))
lem ⊥ i = inr (λ x → x)
lem (V a) i with i a
... | true = inl refl
... | false = inr (λ ())
lem (f ∧ g) i with lem f i | lem g i
... | inl x | inl y = inl (x , y)
... | inl x | inr y = inr (λ (sf , sg) → y sg)
... | inr x | _ = inr (λ (sf , sg) → x sf)
lem (f ∨ g) i with lem f i | lem g i
... | inl x | _ = inl (inl x)
... | inr x | inl y = inl (inr y)
... | inr x | inr y = inr [ x , y ]
lem (f ⇒ g) i with lem f i | lem g i
... | inl x | inl y = inl (λ _ → y)
... | inl x | inr y = inr (λ f2g → y (f2g x))
... | inr x | inl y = inl (λ _ → y)
... | inr x | inr y = inl (λ p → Ø-elim (x p))
