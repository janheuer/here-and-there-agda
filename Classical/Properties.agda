module Classical.Properties where

open import Agda.Builtin.Equality using (refl)
open import Data.Bool renaming (Bool to 𝔹) using (true ; false)
open import Data.Product renaming (proj₁ to p1 ; proj₂ to p2) using (_×_ ; _,_)
open import Data.Sum renaming (inj₁ to inl ; inj₂ to inr) using (_⊎_ ; [_,_])
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim) using ()

open import Classical.Base

dec-C : (f : F) → (i : IPC) → (i ⊧C f) ⊎ ((i ⊧C f) → Ø)
dec-C ⊥ i = inr (λ ())
dec-C (V a) i with i a
... | true = inl refl
... | false = inr (λ ())
dec-C (f ∧ g) i with dec-C f i | dec-C g i
... | inl i⊧f | inl i⊧g = inl (i⊧f , i⊧g)
... | inl i⊧f | inr i⊭g = inr (λ (_ , i⊧g) → i⊭g i⊧g)
... | inr i⊭f | _       = inr (λ (i⊧f , _) → i⊭f i⊧f)
dec-C (f ∨ g) i with dec-C f i | dec-C g i
... | inl i⊧f | _       = inl (inl i⊧f)
... | inr i⊭f | inl i⊧g = inl (inr i⊧g)
... | inr i⊭f | inr i⊭g = inr [ i⊭f , i⊭g ]
dec-C (f ⇒ g) i with dec-C f i | dec-C g i
... | inl i⊧f | inl i⊧g = inl (λ _ → i⊧g)
... | inl i⊧f | inr i⊭g = inr (λ i⊧f⇒g → i⊭g (i⊧f⇒g i⊧f))
... | inr i⊭f | _       = inl (λ i⊧f → Ø-elim (i⊭f i⊧f))
