module Formula.Language where

open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Agda.Builtin.Unit using (tt)
open import Relation.Nullary using (Dec ; yes ; no)
open import Data.Bool renaming (Bool to 𝔹) using (false)
open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Data.Product renaming (proj₁ to p1 ; proj₂ to p2) using (_×_ ; _,_ ; Σ-syntax)
open import Data.Sum renaming (inj₁ to inl ; inj₂ to inr) using (_⊎_ ; [_,_])
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim) using ()

open import Formula.Base
open import Formula.Decidable

-- variable is element of a formula
_∈-F_ : Var → F → Set
a ∈-F ⊥ = Ø
a ∈-F V x = a ≡ x
a ∈-F (f ∧ g) = (a ∈-F f) ⊎ (a ∈-F g)
a ∈-F (f ∨ g) = (a ∈-F f) ⊎ (a ∈-F g)
a ∈-F (f ⇒ g) = (a ∈-F f) ⊎ (a ∈-F g)

-- type of languages languages
Lang : Set
Lang = List Var

-- union of languages
_∪_ : Lang → Lang → Lang
l1 ∪ l2 = l1 ++ l2

-- inclusion in language
_∈-L_ : Var → Lang → Set
a ∈-L [] = Ø
a ∈-L (x ∷ l) = (a ≡ x) ⊎ (a ∈-L l)

-- subset relation for languages
_⊆-L_ : Lang → Lang → Set
l1 ⊆-L l2 = (a : Var) → (a ∈-L l1) → (a ∈-L l2)

trans-⊆-L : {l1 l2 l3 : Lang} → l1 ⊆-L l2 → l2 ⊆-L l3 → l1 ⊆-L l3
trans-⊆-L {l1} {l2} {l3} l1⊆l2 l2⊆l3 a a∈l1 = a∈l3
  where
    a∈l2 = l1⊆l2 a a∈l1
    a∈l3 = l2⊆l3 a a∈l2

-- inclusion in union of languages
∈-L-∪ : (l1 l2 : Lang) → (a : Var) → ((a ∈-L l1) ⊎ (a ∈-L l2)) → a ∈-L (l1 ∪ l2)
∈-L-∪ [] l2 a (inr a∈l2) = a∈l2
∈-L-∪ (x ∷ l1) l2 a (inl (inl a≡x)) = inl a≡x
∈-L-∪ (x ∷ l1) l2 a (inl (inr a∈l1)) = inr (∈-L-∪ l1 l2 a (inl a∈l1))
∈-L-∪ (x1 ∷ l1) l2 a (inr a∈l2) = inr (∈-L-∪ l1 l2 a (inr a∈l2))

∪-L-∈ : (l1 l2 : Lang) → (a : Var) → (a ∈-L (l1 ∪ l2)) → (a ∈-L l1) ⊎ (a ∈-L l2)
∪-L-∈ [] l2 a a∈l1∪l2 = inr a∈l1∪l2
∪-L-∈ (x ∷ l1) l2 a (inl a≡x) = inl (inl a≡x)
∪-L-∈ (x ∷ l1) l2 a (inr a∈l1∪l2) with ∪-L-∈ l1 l2 a a∈l1∪l2
... | inl a∈l1 = inl (inr a∈l1)
... | inr a∈l2 = inr a∈l2

-- language of a formula
_is-lang-of_ : (l : Lang) → (f : F) → Set
l is-lang-of f = (a : Var) → (a ∈-F f) → (a ∈-L l)

lang : (f : F) → Σ[ l ∈ Lang ] (l is-lang-of f)
lang ⊥ = [] , λ a a∈⊥ → a∈⊥
lang (V a) = (a ∷ []) , λ b b≡a → inl b≡a
lang (f ∧ g) = l , l-is-lang-of-f∧g
  where
    lf = p1 (lang f)
    lf-is-lang-of-f = p2 (lang f)

    lg = p1 (lang g)
    lg-is-lang-of-g = p2 (lang g)

    l = lf ∪ lg
    l-is-lang-of-f∧g : l is-lang-of (f ∧ g)
    l-is-lang-of-f∧g a (inl a∈f) = ∈-L-∪ lf lg a (inl (lf-is-lang-of-f a a∈f))
    l-is-lang-of-f∧g a (inr a∈g) = ∈-L-∪ lf lg a (inr (lg-is-lang-of-g a a∈g))
lang (f ∨ g) = l , l-is-lang-of-f∧g
  where
    lf = p1 (lang f)
    lf-is-lang-of-f = p2 (lang f)

    lg = p1 (lang g)
    lg-is-lang-of-g = p2 (lang g)

    l = lf ∪ lg
    l-is-lang-of-f∧g : l is-lang-of (f ∧ g)
    l-is-lang-of-f∧g a (inl a∈f) = ∈-L-∪ lf lg a (inl (lf-is-lang-of-f a a∈f))
    l-is-lang-of-f∧g a (inr a∈g) = ∈-L-∪ lf lg a (inr (lg-is-lang-of-g a a∈g))
lang (f ⇒ g) = l , l-is-lang-of-f∧g
  where
    lf = p1 (lang f)
    lf-is-lang-of-f = p2 (lang f)

    lg = p1 (lang g)
    lg-is-lang-of-g = p2 (lang g)

    l = lf ∪ lg
    l-is-lang-of-f∧g : l is-lang-of (f ∧ g)
    l-is-lang-of-f∧g a (inl a∈f) = ∈-L-∪ lf lg a (inl (lf-is-lang-of-f a a∈f))
    l-is-lang-of-f∧g a (inr a∈g) = ∈-L-∪ lf lg a (inr (lg-is-lang-of-g a a∈g))

lang-of : F → Lang
lang-of f = p1 (lang f)

-- decidability of inclusion in language
∈-L-dec : (a : Var) → (l : Lang) → (a ∈-L l) ⊎ ((a ∈-L l) → Ø)
∈-L-dec a [] = inr λ ()
∈-L-dec a (x ∷ xs) with a ≡Var? x
... | yes a≡x = inl (inl a≡x)
... | no  a≢x with ∈-L-dec a xs
∈-L-dec a (x ∷ xs) | no a≢x | inl a∈xs = inl (inr a∈xs)
∈-L-dec a (x ∷ xs) | no a≢x | inr a∉xs = inr [ a≢x , a∉xs ]

-- equivalence ∈-F and ∈-L
-- i.e. a is in a formula f iff a is in the language of f
∈-F-to-∈-L : (f : F) → (a : Var) → (a ∈-F f) → (a ∈-L (lang-of f))
∈-F-to-∈-L f a a∈f = a∈lf
  where
    lf = p1 (lang f)
    lf-is-lang-of-f = p2 (lang f)

    a∈lf : a ∈-L lf
    a∈lf = lf-is-lang-of-f a a∈f

∈-L-to-∈-F : (f : F) → (a : Var) → (a ∈-L (lang-of f)) → (a ∈-F f)
∈-L-to-∈-F (V x) a (inl a≡x) = a≡x
∈-L-to-∈-F (f ∧ g) a a∈lf∧g with ∪-L-∈ (lang-of f) (lang-of g) a a∈lf∧g
... | inl a∈lf = inl (∈-L-to-∈-F f a a∈lf)
... | inr a∈lg = inr (∈-L-to-∈-F g a a∈lg)
∈-L-to-∈-F (f ∨ g) a a∈lf∨g with ∪-L-∈ (lang-of f) (lang-of g) a a∈lf∨g
... | inl a∈lf = inl (∈-L-to-∈-F f a a∈lf)
... | inr a∈lg = inr (∈-L-to-∈-F g a a∈lg)
∈-L-to-∈-F (f ⇒ g) a a∈lf⇒g with ∪-L-∈ (lang-of f) (lang-of g) a a∈lf⇒g
... | inl a∈lf = inl (∈-L-to-∈-F f a a∈lf)
... | inr a∈lg = inr (∈-L-to-∈-F g a a∈lg)

-- increasing formula increases language
-- i.e. if a in language of f then a also in language of f ∘ g where ∘ ∈ {∧, ∨, ⇒}
lang-∧-⊆ : (f g : F) → (lang-of f) ⊆-L (lang-of (f ∧ g))
lang-∧-⊆ f g a a∈lf = a∈lf∧g
  where
    a∈f = ∈-L-to-∈-F f a a∈lf

    lf∧g = p1 (lang (f ∧ g))
    lf∧g-is-lang-of-f∧g = p2 (lang (f ∧ g))

    a∈lf∧g = lf∧g-is-lang-of-f∧g a (inl a∈f)

lang-∧ˢ-⊆ : (f g : F) → (lang-of g) ⊆-L (lang-of (f ∧ g))
lang-∧ˢ-⊆ f g a a∈lg = a∈lf∧g
  where
    a∈g = ∈-L-to-∈-F g a a∈lg

    lf∧g = p1 (lang (f ∧ g))
    lf∧g-is-lang-of-f∧g = p2 (lang (f ∧ g))

    a∈lf∧g = lf∧g-is-lang-of-f∧g a (inr a∈g)

lang-∨-⊆ : (f g : F) → (lang-of f) ⊆-L (lang-of (f ∨ g))
lang-∨-⊆ f g a a∈lf = a∈lf∨g
  where
    a∈f = ∈-L-to-∈-F f a a∈lf

    lf∨g = p1 (lang (f ∨ g))
    lf∨g-is-lang-of-f∨g = p2 (lang (f ∨ g))

    a∈lf∨g = lf∨g-is-lang-of-f∨g a (inl a∈f)

lang-∨ˢ-⊆ : (f g : F) → (lang-of g) ⊆-L (lang-of (f ∨ g))
lang-∨ˢ-⊆ f g a a∈lg = a∈lf∨g
  where
    a∈g = ∈-L-to-∈-F g a a∈lg

    lf∨g = p1 (lang (f ∨ g))
    lf∨g-is-lang-of-f∨g = p2 (lang (f ∨ g))

    a∈lf∨g = lf∨g-is-lang-of-f∨g a (inr a∈g)

lang-⇒-⊆ : (f g : F) → (lang-of f) ⊆-L (lang-of (f ⇒ g))
lang-⇒-⊆ f g a a∈lf = a∈lf⇒g
  where
    a∈f = ∈-L-to-∈-F f a a∈lf

    lf⇒g = p1 (lang (f ⇒ g))
    lf⇒g-is-lang-of-f⇒g = p2 (lang (f ⇒ g))

    a∈lf⇒g = lf⇒g-is-lang-of-f⇒g a (inl a∈f)

lang-⇒ˢ-⊆ : (f g : F) → (lang-of g) ⊆-L (lang-of (f ⇒ g))
lang-⇒ˢ-⊆ f g a a∈lg = a∈lf⇒g
  where
    a∈g = ∈-L-to-∈-F g a a∈lg

    lf⇒g = p1 (lang (f ⇒ g))
    lf⇒g-is-lang-of-f⇒g = p2 (lang (f ⇒ g))

    a∈lf⇒g = lf⇒g-is-lang-of-f⇒g a (inr a∈g)
