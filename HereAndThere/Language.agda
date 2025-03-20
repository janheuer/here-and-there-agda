module HereAndThere.Language where

open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Agda.Builtin.Unit using (tt)
open import Data.Bool renaming (Bool to 𝔹) using (true ; false)
open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Data.Product renaming (proj₁ to p1 ; proj₂ to p2) using (_×_ ; _,_ ; Σ-syntax)
open import Data.Sum renaming (inj₁ to inl ; inj₂ to inr) using (_⊎_ ; [_,_])
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim) using ()

open import HereAndThere.Base

-- restrict ht interpretation to a language
_||L_ : IPHT → Lang → IPHT
(IHT h t p) ||L l = IHT h|l t|l p|l
  where
    h|l = h |L l
    t|l = t |L l

    p|l : (a : Var) → (h|l a ≡ true) → (t|l a ≡ true)
    p|l a h|la≡true with ∈-L-dec a l
    ... | inl a∈l = p a h|la≡true

-- restrict ht interpretation to the language of a formula
_||F_ : IPHT → F → IPHT
i ||F f = i ||L (lang-of f)

-- i|f ⊧HT f if and only if i|f+ ⊧HT f where f ⊆ f+
i|f⊧HTf-imp-i|f+⊧HTf : (f : F) → (i : IPHT) → (l : Lang) → (lang-of f) ⊆-L l → (i ||F f) ⊧HT f → (i ||L l) ⊧HT f
i|f+⊧HTf-imp-i|f⊧HTf : (f : F) → (i : IPHT) → (l : Lang) → (lang-of f) ⊆-L l → (i ||L l) ⊧HT f → (i ||F f) ⊧HT f

i|f⊧HTf-imp-i|f+⊧HTf = {!!}

i|f+⊧HTf-imp-i|f⊧HTf = {!!}

-- restriction to languages preserves satisfiability
-- i.e. i ⊧HT f if and only if i|f ⊧HT f
i⊧HTf-imp-i|f⊧HTf : (f : F) → (i : IPHT) → i ⊧HT f → (i ||F f) ⊧HT f
i|f⊧HTf-imp-i⊧HTf : (f : F) → (i : IPHT) → (i ||F f) ⊧HT f → i ⊧HT f

i⊧HTf-imp-i|f⊧HTf = {!!}

i|f⊧HTf-imp-i⊧HTf = {!!}
