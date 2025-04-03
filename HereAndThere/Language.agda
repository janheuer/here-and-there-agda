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

-- let f be a formula and f+ a language such that f ⊆ f+
-- then i|f ⊧HT f if and only if i|f+ ⊧HT f where f ⊆ f+
-- i.e. an interpretation i restricted to f is a model of f
-- if and only if i restricted to any bigger language is also a model
i|f⊧HTf-imp-i|f+⊧HTf : (f : F) → (i : IPHT) → (l : Lang) → (lang-of f) ⊆-L l → (i ||F f) ⊧HT f → (i ||L l) ⊧HT f
i|f+⊧HTf-imp-i|f⊧HTf : (f : F) → (i : IPHT) → (l : Lang) → (lang-of f) ⊆-L l → (i ||L l) ⊧HT f → (i ||F f) ⊧HT f

i|f⊧HTf-imp-i|f+⊧HTf (V a) i l a⊆l i|a⊧a = i|l⊧a
  where
    a∈l = a⊆l a (inl refl)
    i|l = i ||L l

    iha≡true : (ph i) a ≡ true
    iha≡true with ∈-L-dec a (lang-of (V a))
    ... | inl a∈a = i|a⊧a

    i|l⊧a : (ph i|l) a ≡ true
    i|l⊧a with ∈-L-dec a l
    ... | inl a∈l = iha≡true
    ... | inr a∉l = Ø-elim (a∉l a∈l)
i|f⊧HTf-imp-i|f+⊧HTf (f ∧ g) i l f∧g⊆l (i|f∧g⊧f , i|f∧g⊧g) = i|l⊧f , i|l⊧g
  where
    f⊆f∧g = lang-∧-⊆ f g
    f⊆l = trans-⊆-L f⊆f∧g f∧g⊆l
    i|f⊧f = i|f+⊧HTf-imp-i|f⊧HTf f i (lang-of (f ∧ g)) f⊆f∧g i|f∧g⊧f
    i|l⊧f = i|f⊧HTf-imp-i|f+⊧HTf f i l f⊆l i|f⊧f

    g⊆f∧g = lang-∧ˢ-⊆ f g
    g⊆l = trans-⊆-L g⊆f∧g f∧g⊆l
    i|g⊧g = i|f+⊧HTf-imp-i|f⊧HTf g i (lang-of (f ∧ g)) g⊆f∧g i|f∧g⊧g
    i|l⊧g = i|f⊧HTf-imp-i|f+⊧HTf g i l g⊆l i|g⊧g
i|f⊧HTf-imp-i|f+⊧HTf (f ∨ g) i l f∨g⊆l (inl i|f∨g⊧f) = inl i|l⊧f
  where
    f⊆f∨g = lang-∨-⊆ f g
    f⊆l = trans-⊆-L f⊆f∨g f∨g⊆l
    i|f⊧f = i|f+⊧HTf-imp-i|f⊧HTf f i (lang-of (f ∨ g)) f⊆f∨g i|f∨g⊧f
    i|l⊧f = i|f⊧HTf-imp-i|f+⊧HTf f i l f⊆l i|f⊧f
i|f⊧HTf-imp-i|f+⊧HTf (f ∨ g) i l f∨g⊆l (inr i|f∨g⊧g) = inr i|l⊧g
  where
    g⊆f∨g = lang-∨ˢ-⊆ f g
    g⊆l = trans-⊆-L g⊆f∨g f∨g⊆l
    i|g⊧g = i|f+⊧HTf-imp-i|f⊧HTf g i (lang-of (f ∨ g)) g⊆f∨g i|f∨g⊧g
    i|l⊧g = i|f⊧HTf-imp-i|f+⊧HTf g i l g⊆l i|g⊧g
i|f⊧HTf-imp-i|f+⊧HTf (f ⇒ g) i@(IHT h t p) l f⇒g⊆l (i|f⇒g⊧HTf⇒g , t|f⇒g⊧Cf⇒g) = i|l⊧HTf⇒g , t|l⊧Cf⇒g
  where
    i|l = i ||L l
    t|l = pt i|l

    i|l⊧HTf⇒g : i|l ⊧HT f → i|l ⊧HT g
    i|l⊧HTf⇒g i|l⊧HTf = i|l⊧HTg
      where
        f⊆f⇒g = lang-⇒-⊆ f g
        f⊆l = trans-⊆-L f⊆f⇒g f⇒g⊆l
        i|f⊧HTf = i|f+⊧HTf-imp-i|f⊧HTf f i l f⊆l i|l⊧HTf
        i|f⇒g⊧HTf = i|f⊧HTf-imp-i|f+⊧HTf f i (lang-of (f ⇒ g)) f⊆f⇒g i|f⊧HTf

        g⊆f⇒g = lang-⇒ˢ-⊆ f g
        g⊆l = trans-⊆-L g⊆f⇒g f⇒g⊆l
        i|f⇒g⊧HTg = i|f⇒g⊧HTf⇒g i|f⇒g⊧HTf
        i|g⊧HTg = i|f+⊧HTf-imp-i|f⊧HTf g i (lang-of (f ⇒ g)) g⊆f⇒g i|f⇒g⊧HTg
        i|l⊧HTg = i|f⊧HTf-imp-i|f+⊧HTf g i l g⊆l i|g⊧HTg

    t|l⊧Cf⇒g : t|l ⊧C (f ⇒ g)
    t|l⊧Cf⇒g = i|f⊧Cf-imp-i|f+⊧Cf (f ⇒ g) t l f⇒g⊆l t|f⇒g⊧Cf⇒g

i|f+⊧HTf-imp-i|f⊧HTf (V a) i@(IHT h t p) l a⊆l i|l⊧a = i|a⊧a
  where
    i|a = i ||F (V a)

    ha≡true : h a ≡ true
    ha≡true with ∈-L-dec a l
    ... | inl a∈l = i|l⊧a

    i|a⊧a : (ph i|a) a ≡ true
    i|a⊧a with ∈-L-dec a (lang-of (V a))
    ... | inl a∈a = ha≡true
    ... | inr a∉a = Ø-elim (a∉a (inl refl))
i|f+⊧HTf-imp-i|f⊧HTf (f ∧ g) i l f∧g⊆l (i|l⊧f , i|l⊧g) = i|f∧g⊧f , i|f∧g⊧g
  where
    f⊆f∧g = lang-∧-⊆ f g
    f⊆l = trans-⊆-L f⊆f∧g f∧g⊆l
    i|f⊧f = i|f+⊧HTf-imp-i|f⊧HTf f i l f⊆l i|l⊧f
    i|f∧g⊧f = i|f⊧HTf-imp-i|f+⊧HTf f i (lang-of (f ∧ g)) f⊆f∧g i|f⊧f

    g⊆f∧g = lang-∧ˢ-⊆ f g
    g⊆l = trans-⊆-L g⊆f∧g f∧g⊆l
    i|g⊧g = i|f+⊧HTf-imp-i|f⊧HTf g i l g⊆l i|l⊧g
    i|f∧g⊧g = i|f⊧HTf-imp-i|f+⊧HTf g i (lang-of (f ∧ g)) g⊆f∧g i|g⊧g
i|f+⊧HTf-imp-i|f⊧HTf (f ∨ g) i l f∨g⊆l (inl i|l⊧f) = inl i|f∨g⊧f
  where
    f⊆f∨g = lang-∨-⊆ f g
    f⊆l = trans-⊆-L f⊆f∨g f∨g⊆l
    i|f⊧f = i|f+⊧HTf-imp-i|f⊧HTf f i l f⊆l i|l⊧f
    i|f∨g⊧f = i|f⊧HTf-imp-i|f+⊧HTf f i (lang-of (f ∨ g)) f⊆f∨g i|f⊧f
i|f+⊧HTf-imp-i|f⊧HTf (f ∨ g) i l f∨g⊆l (inr i|l⊧g) = inr i|f∨g⊧g
  where
    g⊆f∨g = lang-∨ˢ-⊆ f g
    g⊆l = trans-⊆-L g⊆f∨g f∨g⊆l
    i|g⊧g = i|f+⊧HTf-imp-i|f⊧HTf g i l g⊆l i|l⊧g
    i|f∨g⊧g = i|f⊧HTf-imp-i|f+⊧HTf g i (lang-of (f ∨ g)) g⊆f∨g i|g⊧g
i|f+⊧HTf-imp-i|f⊧HTf (f ⇒ g) i@(IHT h t p) l f⇒g⊆l (i|l⊧HTf⇒g , t|l⊧Cf⇒g) = i|f⇒g⊧HTf⇒g , t|f⇒g⊧Cf⇒g
  where
    i|f⇒g = i ||F (f ⇒ g)
    t|f⇒g = pt i|f⇒g

    i|f⇒g⊧HTf⇒g : i|f⇒g ⊧HT f → i|f⇒g ⊧HT g
    i|f⇒g⊧HTf⇒g i|f⇒g⊧HTf = i|f⇒g⊧HTg
      where
        f⊆f⇒g = lang-⇒-⊆ f g
        f⊆l = trans-⊆-L f⊆f⇒g f⇒g⊆l
        i|f⊧HTf = i|f+⊧HTf-imp-i|f⊧HTf f i (lang-of (f ⇒ g)) f⊆f⇒g i|f⇒g⊧HTf
        i|l⊧HTf = i|f⊧HTf-imp-i|f+⊧HTf f i l f⊆l i|f⊧HTf

        g⊆f⇒g = lang-⇒ˢ-⊆ f g
        g⊆l = trans-⊆-L g⊆f⇒g f⇒g⊆l
        i|l⊧HTg = i|l⊧HTf⇒g i|l⊧HTf
        i|g⊧HTg = i|f+⊧HTf-imp-i|f⊧HTf g i l g⊆l i|l⊧HTg
        i|f⇒g⊧HTg = i|f⊧HTf-imp-i|f+⊧HTf g i (lang-of (f ⇒ g)) g⊆f⇒g i|g⊧HTg

    t|f⇒g⊧Cf⇒g : t|f⇒g ⊧C (f ⇒ g)
    t|f⇒g⊧Cf⇒g = i|f+⊧Cf-imp-i|f⊧Cf (f ⇒ g) t l f⇒g⊆l t|l⊧Cf⇒g

-- restriction to languages preserves satisfiability
-- i.e. i ⊧HT f if and only if i|f ⊧HT f
i⊧HTf-imp-i|f⊧HTf : (f : F) → (i : IPHT) → i ⊧HT f → (i ||F f) ⊧HT f
i|f⊧HTf-imp-i⊧HTf : (f : F) → (i : IPHT) → (i ||F f) ⊧HT f → i ⊧HT f

i⊧HTf-imp-i|f⊧HTf = {!!}

i|f⊧HTf-imp-i⊧HTf = {!!}
