module Classical.Language where

open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Agda.Builtin.Unit using (tt)
open import Data.Bool renaming (Bool to 𝔹) using (true ; false)
open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Data.Product renaming (proj₁ to p1 ; proj₂ to p2) using (_×_ ; _,_ ; Σ-syntax)
open import Data.Sum renaming (inj₁ to inl ; inj₂ to inr) using (_⊎_ ; [_,_])
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim) using ()

open import Classical.Base

-- restrict interpretation to a language
_|L_ : IPC → Lang → IPC
i |L l = i|l
  where
    i|l : IPC
    i|l a with ∈-L-dec a l
    ... | inl a∈l = i a
    ... | inr a∉l = false

-- restrict interpretation to the language of a formula
_|F_ : IPC → F → IPC
i |F f = i |L (lang-of f)

-- i|f ⊧C f iff i|f+ ⊧C f where f ⊆ f+
i|f⊧Cf-imp-i|f+⊧Cf : (f : F) → (i : IPC) → (l : Lang) → (lang-of f) ⊆-L l → (i |F f) ⊧C f → (i |L l) ⊧C f
i|f+⊧Cf-imp-i|f⊧Cf : (f : F) → (i : IPC) → (l : Lang) → (lang-of f) ⊆-L l → (i |L l) ⊧C f → (i |F f) ⊧C f

i|f⊧Cf-imp-i|f+⊧Cf (V a) i l a⊆l i|a⊧a = i|l⊧a
  where
    a∈l = a⊆l a (inl refl)
    i|l = i |L l

    ia≡true : i a ≡ true
    ia≡true with ∈-L-dec a (lang-of (V a))
    ... | inl a∈a = i|a⊧a

    i|l⊧a : i|l a ≡ true
    i|l⊧a with ∈-L-dec a l
    ... | inl a∈l = ia≡true
    ... | inr a∉l = Ø-elim (a∉l a∈l)
i|f⊧Cf-imp-i|f+⊧Cf (f ∧ g) i l f∧g⊆l (i|f∧g⊧f , i|f∧g⊧g) = i|l⊧f , i|l⊧g
  where
    f⊆f∧g = lang-∧-⊆ f g
    f⊆l = trans-⊆-L f⊆f∧g f∧g⊆l
    i|f⊧f = i|f+⊧Cf-imp-i|f⊧Cf f i (lang-of (f ∧ g)) f⊆f∧g i|f∧g⊧f
    i|l⊧f = i|f⊧Cf-imp-i|f+⊧Cf f i l f⊆l i|f⊧f

    g⊆f∧g = lang-∧ˢ-⊆ f g
    g⊆l = trans-⊆-L g⊆f∧g f∧g⊆l
    i|g⊧g = i|f+⊧Cf-imp-i|f⊧Cf g i (lang-of (f ∧ g)) g⊆f∧g i|f∧g⊧g
    i|l⊧g = i|f⊧Cf-imp-i|f+⊧Cf g i l g⊆l i|g⊧g
i|f⊧Cf-imp-i|f+⊧Cf (f ∨ g) i l f∨g⊆l (inl i|f∨g⊧f) = inl i|l⊧f
  where
    f⊆f∨g = lang-∨-⊆ f g
    f⊆l = trans-⊆-L f⊆f∨g f∨g⊆l
    i|f⊧f = i|f+⊧Cf-imp-i|f⊧Cf f i (lang-of (f ∨ g)) f⊆f∨g i|f∨g⊧f
    i|l⊧f = i|f⊧Cf-imp-i|f+⊧Cf f i l f⊆l i|f⊧f
i|f⊧Cf-imp-i|f+⊧Cf (f ∨ g) i l f∨g⊆l (inr i|f∨g⊧g) = inr i|l⊧g
  where
    g⊆f∨g = lang-∨ˢ-⊆ f g
    g⊆l = trans-⊆-L g⊆f∨g f∨g⊆l
    i|g⊧g = i|f+⊧Cf-imp-i|f⊧Cf g i (lang-of (f ∨ g)) g⊆f∨g i|f∨g⊧g
    i|l⊧g = i|f⊧Cf-imp-i|f+⊧Cf g i l g⊆l i|g⊧g
i|f⊧Cf-imp-i|f+⊧Cf (f ⇒ g) i l f⇒g⊆l i|f⇒g⊧f⇒g i|l⊧f = i|l⊧g
  where
    f⊆f⇒g = lang-⇒-⊆ f g
    f⊆l = trans-⊆-L f⊆f⇒g f⇒g⊆l
    i|f⊧f = i|f+⊧Cf-imp-i|f⊧Cf f i l f⊆l i|l⊧f
    i|f⇒g⊧f = i|f⊧Cf-imp-i|f+⊧Cf f i (lang-of (f ⇒ g)) f⊆f⇒g i|f⊧f

    g⊆f⇒g = lang-⇒ˢ-⊆ f g
    g⊆l = trans-⊆-L g⊆f⇒g f⇒g⊆l
    i|f⇒g⊧g = i|f⇒g⊧f⇒g i|f⇒g⊧f
    i|g⊧g = i|f+⊧Cf-imp-i|f⊧Cf g i (lang-of (f ⇒ g)) g⊆f⇒g i|f⇒g⊧g
    i|l⊧g = i|f⊧Cf-imp-i|f+⊧Cf g i l g⊆l i|g⊧g

i|f+⊧Cf-imp-i|f⊧Cf (V a) i l a⊆l i|l⊧a = i|a⊧a
  where
    i|a = i |F (V a)

    ia≡true : i a ≡ true
    ia≡true with ∈-L-dec a l
    ... | inl _ = i|l⊧a

    i|a⊧a : i|a a ≡ true
    i|a⊧a with ∈-L-dec a (lang-of (V a))
    ... | inl a∈a = ia≡true
    ... | inr a∉a = Ø-elim (a∉a (inl refl))
i|f+⊧Cf-imp-i|f⊧Cf (f ∧ g) i l f∧g⊆l (i|l⊧f , i|l⊧g) = i|f∧g⊧f , i|f∧g⊧g
  where
    f⊆f∧g = lang-∧-⊆ f g
    f⊆l = trans-⊆-L f⊆f∧g f∧g⊆l
    i|f⊧f = i|f+⊧Cf-imp-i|f⊧Cf f i l f⊆l i|l⊧f
    i|f∧g⊧f = i|f⊧Cf-imp-i|f+⊧Cf f i (lang-of (f ∧ g)) f⊆f∧g i|f⊧f

    g⊆f∧g = lang-∧ˢ-⊆ f g
    g⊆l = trans-⊆-L g⊆f∧g f∧g⊆l
    i|g⊧g = i|f+⊧Cf-imp-i|f⊧Cf g i l g⊆l i|l⊧g
    i|f∧g⊧g = i|f⊧Cf-imp-i|f+⊧Cf g i (lang-of (f ∧ g)) g⊆f∧g i|g⊧g
i|f+⊧Cf-imp-i|f⊧Cf (f ∨ g) i l f∨g⊆l (inl i|l⊧f) = inl i|f∨g⊧f
  where
    f⊆f∨g = lang-∨-⊆ f g
    f⊆l = trans-⊆-L f⊆f∨g f∨g⊆l
    i|f⊧f = i|f+⊧Cf-imp-i|f⊧Cf f i l f⊆l i|l⊧f
    i|f∨g⊧f = i|f⊧Cf-imp-i|f+⊧Cf f i (lang-of (f ∨ g)) f⊆f∨g i|f⊧f
i|f+⊧Cf-imp-i|f⊧Cf (f ∨ g) i l f∨g⊆l (inr i|l⊧g) = inr i|f∨g⊧g
  where
    g⊆f∨g = lang-∨ˢ-⊆ f g
    g⊆l = trans-⊆-L g⊆f∨g f∨g⊆l
    i|g⊧g = i|f+⊧Cf-imp-i|f⊧Cf g i l g⊆l i|l⊧g
    i|f∨g⊧g = i|f⊧Cf-imp-i|f+⊧Cf g i (lang-of (f ∨ g)) g⊆f∨g i|g⊧g
i|f+⊧Cf-imp-i|f⊧Cf (f ⇒ g) i l f⇒g⊆l i|l⊧f⇒g i|f⇒g⊧f = i|f⇒g⊧g
  where
    f⊆f⇒g = lang-⇒-⊆ f g
    f⊆l = trans-⊆-L f⊆f⇒g f⇒g⊆l
    i|f⊧f = i|f+⊧Cf-imp-i|f⊧Cf f i (lang-of (f ⇒ g)) f⊆f⇒g i|f⇒g⊧f
    i|l⊧f = i|f⊧Cf-imp-i|f+⊧Cf f i l f⊆l i|f⊧f

    g⊆f⇒g = lang-⇒ˢ-⊆ f g
    g⊆l = trans-⊆-L g⊆f⇒g f⇒g⊆l
    i|l⊧g = i|l⊧f⇒g i|l⊧f
    i|g⊧g = i|f+⊧Cf-imp-i|f⊧Cf g i l g⊆l i|l⊧g
    i|f⇒g⊧g = i|f⊧Cf-imp-i|f+⊧Cf g i (lang-of (f ⇒ g)) g⊆f⇒g i|g⊧g

-- restriction to languages preserves satisfiability
-- i.e. i ⊧C f if and only if i|f ⊧C f
i⊧Cf-imp-i|f⊧Cf : (f : F) → (i : IPC) → i ⊧C f → (i |F f) ⊧C f
i|f⊧Cf-imp-i⊧Cf : (f : F) → (i : IPC) → (i |F f) ⊧C f → i ⊧C f

i⊧Cf-imp-i|f⊧Cf (V a) i i⊧a = i|a⊧a
  where
    i|a = i |F (V a)
    i|a⊧a : i|a a ≡ true
    i|a⊧a with ∈-L-dec a (lang-of (V a))
    ... | inl a∈a = i⊧a
    ... | inr a∉a = Ø-elim (a∉a (inl refl))
i⊧Cf-imp-i|f⊧Cf (f ∧ g) i (i⊧f , i⊧g) = i|f∧g⊧f∧g
   where
     f⊆f∧g = lang-∧-⊆ f g
     i|f⊧f = i⊧Cf-imp-i|f⊧Cf f i i⊧f
     i|f∧g = i |F (f ∧ g)
     i|f∧g⊧f = i|f⊧Cf-imp-i|f+⊧Cf f i (lang-of (f ∧ g)) f⊆f∧g i|f⊧f

     g⊆f∧g = lang-∧ˢ-⊆ f g
     i|g⊧g = i⊧Cf-imp-i|f⊧Cf g i i⊧g
     i|f∧g⊧g = i|f⊧Cf-imp-i|f+⊧Cf g i (lang-of (f ∧ g)) g⊆f∧g i|g⊧g
     i|f∧g⊧f∧g = i|f∧g⊧f , i|f∧g⊧g
i⊧Cf-imp-i|f⊧Cf (f ∨ g) i (inl i⊧f) = inl i|f∨g⊧f
  where
    f⊆f∨g = lang-∨-⊆ f g
    i|f⊧f = i⊧Cf-imp-i|f⊧Cf f i i⊧f
    i|f∨g = i |F (f ∨ g)
    i|f∨g⊧f = i|f⊧Cf-imp-i|f+⊧Cf f i (lang-of (f ∨ g)) f⊆f∨g i|f⊧f
i⊧Cf-imp-i|f⊧Cf (f ∨ g) i (inr i⊧g) = inr i|f∨g⊧g
  where
    g⊆f∨g = lang-∨ˢ-⊆ f g
    i|g⊧g = i⊧Cf-imp-i|f⊧Cf g i i⊧g
    i|f∨g = i |F (f ∨ g)
    i|f∨g⊧g = i|f⊧Cf-imp-i|f+⊧Cf g i (lang-of (f ∨ g)) g⊆f∨g i|g⊧g
i⊧Cf-imp-i|f⊧Cf (f ⇒ g) i i⊧f⇒g i|f⇒g⊧f = i|f⇒g⊧g
  where
    f⊆f⇒g = lang-⇒-⊆ f g
    i|f⊧f = i|f+⊧Cf-imp-i|f⊧Cf f i (lang-of (f ⇒ g)) f⊆f⇒g i|f⇒g⊧f
    i⊧f = i|f⊧Cf-imp-i⊧Cf f i i|f⊧f

    g⊆f⇒g = lang-⇒ˢ-⊆ f g
    i⊧g = i⊧f⇒g i⊧f
    i|g⊧g = i⊧Cf-imp-i|f⊧Cf g i i⊧g
    i|f⇒g⊧g = i|f⊧Cf-imp-i|f+⊧Cf g i (lang-of (f ⇒ g)) g⊆f⇒g i|g⊧g

i|f⊧Cf-imp-i⊧Cf (V a) i i|a⊧a = i⊧a
  where
    i⊧a : i a ≡ true
    i⊧a with ∈-L-dec a (lang-of (V a))
    ... | inl a∈a = i|a⊧a
i|f⊧Cf-imp-i⊧Cf (f ∧ g) i (i|f∧g⊧f , i|f∧g⊧g) = i⊧f , i⊧g
  where
    f⊆f∧g = lang-∧-⊆ f g
    i|f⊧f = i|f+⊧Cf-imp-i|f⊧Cf f i (lang-of (f ∧ g)) f⊆f∧g i|f∧g⊧f
    i⊧f = i|f⊧Cf-imp-i⊧Cf f i i|f⊧f

    g⊆f∧g = lang-∧ˢ-⊆ f g
    i|g⊧g = i|f+⊧Cf-imp-i|f⊧Cf g i (lang-of (f ∧ g)) g⊆f∧g i|f∧g⊧g
    i⊧g = i|f⊧Cf-imp-i⊧Cf g i i|g⊧g
i|f⊧Cf-imp-i⊧Cf (f ∨ g) i (inl i|f∨g⊧f) = inl i⊧f
  where
    f⊆f∨g = lang-∨-⊆ f g
    i|f⊧f = i|f+⊧Cf-imp-i|f⊧Cf f i (lang-of (f ∨ g)) f⊆f∨g i|f∨g⊧f
    i⊧f = i|f⊧Cf-imp-i⊧Cf f i i|f⊧f
i|f⊧Cf-imp-i⊧Cf (f ∨ g) i (inr i|f∨g⊧g) = inr i⊧g
  where
    g⊆f∨g = lang-∨ˢ-⊆ f g
    i|g⊧g = i|f+⊧Cf-imp-i|f⊧Cf g i (lang-of (f ∨ g)) g⊆f∨g i|f∨g⊧g
    i⊧g = i|f⊧Cf-imp-i⊧Cf g i i|g⊧g
i|f⊧Cf-imp-i⊧Cf (f ⇒ g) i i|f⇒g⊧f⇒g i⊧f = i⊧g
  where
    f⊆f⇒g = lang-⇒-⊆ f g
    i|f⊧f = i⊧Cf-imp-i|f⊧Cf f i i⊧f
    i|f⇒g⊧f = i|f⊧Cf-imp-i|f+⊧Cf f i (lang-of (f ⇒ g)) f⊆f⇒g i|f⊧f

    g⊆f⇒g = lang-⇒ˢ-⊆ f g
    i|f⇒g⊧g = i|f⇒g⊧f⇒g i|f⇒g⊧f
    i|g⊧g = i|f+⊧Cf-imp-i|f⊧Cf g i (lang-of (f ⇒ g)) g⊆f⇒g i|f⇒g⊧g
    i⊧g = i|f⊧Cf-imp-i⊧Cf g i i|g⊧g
