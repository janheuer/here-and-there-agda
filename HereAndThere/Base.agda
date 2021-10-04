module HereAndThere.Base where

open import Agda.Builtin.Equality public
open import Agda.Builtin.Sigma public
open import Data.Bool renaming (Bool to 𝔹 ; _∧_ to _∧𝔹_ ; _∨_ to _∨𝔹_ ;
                                not to ¬𝔹) public
open import Data.List using (List ; _∷_ ; []) public
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim) public
open import Data.Sum using (_⊎_ ; [_,_])
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
-- using element relation
_⊨HT∈_ : IPHT → Th → Set
i ⊨HT∈ t = (f : F) → f ∈ t → i ⊧HT f

-- using conversion to conjunction of elements
_⊨HT∧_ : IPHT → Th → Set
i ⊨HT∧ t = i ⊧HT (Th2F t)

-- equivalence proof
⊨HT∈-to-⊨HT∧ : (i : IPHT) → (t : Th) → i ⊨HT∈ t → i ⊨HT∧ t
⊨HT∈-to-⊨HT∧ i [] _ = (λ ()) , (λ ())
⊨HT∈-to-⊨HT∧ i (f ∷ t) i⊨HTt = i⊨HTt f (inl refl) ,
                               ⊨HT∈-to-⊨HT∧ i t (λ f f∈t → i⊨HTt f (inr f∈t))

⊨HT∧-to-⊨HT∈ : (i : IPHT) → (t : Th) → i ⊨HT∧ t → i ⊨HT∈ t
⊨HT∧-to-⊨HT∈ i (f ∷ t) (i⊧HTf , _) .f (inl refl) = i⊧HTf
⊨HT∧-to-⊨HT∈ i (f ∷ t) (_ , i⊨HT't) g (inr g∈t) = ⊨HT∧-to-⊨HT∈ i t i⊨HT't g g∈t
