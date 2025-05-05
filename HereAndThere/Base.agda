module HereAndThere.Base where

open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Data.Bool renaming (Bool to 𝔹) using (true)
open import Data.Empty renaming (⊥ to Ø) using ()
open import Data.Product using (_×_ ; _,_)
open import Data.Sum using (_⊎_) renaming (inj₁ to inl ; inj₂ to inr)
open import Data.List using (List ; [] ; _∷_)

open import Formula public
open import Classical public

-- here-and-there interpretations ----------------------------------------------
-- ht interpretations consist of two classical interpretations h and t, s.t.
-- all atoms true in h are also true in t (h ⊆ t)
-- type for inclusion proofs

-- ht interpretations
record IPHT : Set where
  constructor IHT
  field
    ph : IPC
    pt : IPC
    pi : ph ⊆ pt

open IPHT public

-- shorthand for total here-and-there interpretation
THT : IPC → IPHT
THT t = IHT t t (λ a p → p)

-- satisfiability of formulas in the logic of here-and-there -------------------
_⊧HT_ : IPHT → F → Set
i ⊧HT ⊥ = Ø
(IHT h _ _) ⊧HT (V a) = h a ≡ true
i ⊧HT (f ∧ g) = (i ⊧HT f) × (i ⊧HT g)
i ⊧HT (f ∨ g) = (i ⊧HT f) ⊎ (i ⊧HT g)
i@(IHT _ t _) ⊧HT (f ⇒ g) = ((i ⊧HT f) → (i ⊧HT g)) × (t ⊧C (f ⇒ g))

-- validity of formulas
ValidHT : F → Set
ValidHT f = (i : IPHT) → i ⊧HT f

_≡HT_ : F → F → Set
f ≡HT g = ValidHT (f ⇔ g)
