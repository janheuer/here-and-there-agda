module HereAndThere.Base where

open import Agda.Builtin.Equality public
open import Agda.Builtin.Sigma public
open import Data.Bool renaming (Bool to 𝔹 ; _∧_ to _∧𝔹_ ; _∨_ to _∨𝔹_ ;
                                not to ¬𝔹) public
open import Data.List using (List ; _∷_ ; []) public
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim) public
open import Data.Sum.Base using (_⊎_ ; [_,_])
                          renaming (inj₁ to inl ; inj₂ to inr) public
open import Data.Product using (_×_ ; _,_)
                         renaming (proj₁ to p1 ; proj₂ to p2) public

open import Formula public
open import Classical public

-- here-and-there interpretations ----------------------------------------------
-- ht interpretations consist of two classical interpretations h and t, s.t.
-- all atoms true in h are also true in t (h ⊆ t)
-- type for inclusion proofs
_⊆_ : IPC → IPC → Set
h ⊆ t = (a : Var) → h a ≡ true → t a ≡ true

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

-- extension of ⊧HT to theories
_⊨HT_ : IPHT → Th → Set
i ⊨HT t = (f : F) → f ∈ t → i ⊧HT f
