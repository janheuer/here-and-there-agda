module HereAndThere.Base where

-- definition of ht interpretations and the satisfiability relation

open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Data.Bool renaming (Bool to 𝔹) using (true)
open import Data.Empty renaming (⊥ to Ø) using ()
open import Data.Product using (_×_ ; _,_)
open import Data.Sum using (_⊎_) renaming (inj₁ to inl ; inj₂ to inr)
open import Data.List using (List ; [] ; _∷_)

open import Formula public
open import Classical public

-- here-and-there interpretations ----------------------------------------------
-- ht interpretations
record IPHT : Set where
  constructor IHT
  field
    -- two classical interpretations:
    -- the here interpretation
    ph : IPC
    -- and the there interpretation
    pt : IPC
    -- such that here is a subset of there
    pi : ph ⊆ pt

open IPHT public

-- shorthand for total here-and-there interpretation
THT : IPC → IPHT
THT t = IHT t t (λ a p → p)

-- satisfiability of formulas in the logic of here-and-there -------------------
_⊧HT_ : IPHT → F → Set
-- no interpretation is a model of false
i ⊧HT ⊥                   = Ø
-- for atomic formulas only the here interpretation matters
(IHT h _ _) ⊧HT (V a)     = h a ≡ true
-- a conjunction is satisfied if both component are satisfied
i ⊧HT (f ∧ g)             = (i ⊧HT f) × (i ⊧HT g)
-- a disjunction is satisfied if one component is satisfied
i ⊧HT (f ∨ g)             = (i ⊧HT f) ⊎ (i ⊧HT g)
-- note that so far this is the same as classical satisfaction
-- an interpretation is satisfied if it is satisfied in the ...
-- here: a proof of f can be turned into a proof of g
-- there: the implication holds classically in the there interpretation
-- without this second condition we would have exactly classical logic
i@(IHT _ t _) ⊧HT (f ⇒ g) = ((i ⊧HT f) → (i ⊧HT g)) × (t ⊧C (f ⇒ g))

-- validity of formulas
ValidHT : F → Set
ValidHT f = (i : IPHT) → i ⊧HT f

-- shorthand notation for validity of equivalences
_≡HT_ : F → F → Set
f ≡HT g = ValidHT (f ⇔ g)
