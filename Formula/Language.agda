module Formula.Language where

-- this module defines languages: sets of atoms
-- as well as some operations on languages

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Data.Product renaming (proj₁ to p1 ; proj₂ to p2) using (_×_ ; _,_ ; Σ-syntax)
open import Data.Sum renaming (inj₁ to inl ; inj₂ to inr) using (_⊎_ ; [_,_])
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim) using ()

open import Formula.Base
open import Formula.Decidable

-- elements of a formula
_∈-F_ : Var → F → Set
a ∈-F ⊥ = Ø
a ∈-F V x = a ≡ x
a ∈-F (f ∧ g) = (a ∈-F f) ⊎ (a ∈-F g)
a ∈-F (f ∨ g) = (a ∈-F f) ⊎ (a ∈-F g)
a ∈-F (f ⇒ g) = (a ∈-F f) ⊎ (a ∈-F g)

-- definition of languages and elementary operations ---------------------------
-- type of languages
Lang : Set
-- we simply model languages as lists here for simplicity
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

-- elementary properties of languages-------------------------------------------
-- subset relation is transitive
trans-⊆-L : {l1 l2 l3 : Lang} → l1 ⊆-L l2 → l2 ⊆-L l3 → l1 ⊆-L l3
trans-⊆-L {l1} {l2} {l3} l1⊆l2 l2⊆l3 a a∈l1 = a∈l3
  where
    a∈l2 = l1⊆l2 a a∈l1
    a∈l3 = l2⊆l3 a a∈l2

-- variable a is in the union of l1 and l2 iff a is in l1 or l2
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

-- languages of formulas -------------------------------------------------------
-- l is the language of f
_is-lang-of_ : (l : Lang) → (f : F) → Set
l is-lang-of f = (a : Var) → (a ∈-F f) → (a ∈-L l)

-- obtain language of a formula
lang : (f : F) → Σ[ l ∈ Lang ] (l is-lang-of f)
lang ⊥ = [] , λ a a∈⊥ → a∈⊥
lang (V a) = (a ∷ []) , λ b b∈a → inl b∈a
lang (f ∧ g) = l , l-is-lang-of-f∧g
  where
    -- we start by computing the languages lf of f and lg of g recursively
    lf = p1 (lang f)
    lf-is-lang-of-f = p2 (lang f)

    lg = p1 (lang g)
    lg-is-lang-of-g = p2 (lang g)

    -- the language of the conjunction is then simply the union of lf and lg
    l = lf ∪ lg
    l-is-lang-of-f∧g : l is-lang-of (f ∧ g)
    -- if some a is in the formula f ∧ g it is
    -- 1) in the formula f
    -- then a is also in lf and thus in the union of lf and lg
    l-is-lang-of-f∧g a (inl a∈f) = ∈-L-∪ lf lg a (inl (lf-is-lang-of-f a a∈f))
    -- or 2) in the formula g
    l-is-lang-of-f∧g a (inr a∈g) = ∈-L-∪ lf lg a (inr (lg-is-lang-of-g a a∈g))
-- disjunction and implication are analogous to conjunction
lang (f ∨ g) = l , l-is-lang-of-f∧g
  where
    lf = p1 (lang f)
    lf-is-lang-of-f = p2 (lang f)

    lg = p1 (lang g)
    lg-is-lang-of-g = p2 (lang g)

    l = lf ∪ lg
    l-is-lang-of-f∧g : l is-lang-of (f ∨ g)
    l-is-lang-of-f∧g a (inl a∈f) = ∈-L-∪ lf lg a (inl (lf-is-lang-of-f a a∈f))
    l-is-lang-of-f∧g a (inr a∈g) = ∈-L-∪ lf lg a (inr (lg-is-lang-of-g a a∈g))
lang (f ⇒ g) = l , l-is-lang-of-f∧g
  where
    lf = p1 (lang f)
    lf-is-lang-of-f = p2 (lang f)

    lg = p1 (lang g)
    lg-is-lang-of-g = p2 (lang g)

    l = lf ∪ lg
    l-is-lang-of-f∧g : l is-lang-of (f ⇒ g)
    l-is-lang-of-f∧g a (inl a∈f) = ∈-L-∪ lf lg a (inl (lf-is-lang-of-f a a∈f))
    l-is-lang-of-f∧g a (inr a∈g) = ∈-L-∪ lf lg a (inr (lg-is-lang-of-g a a∈g))

-- shorthand notation for language of a formula without the proof
lang-of : F → Lang
lang-of f = p1 (lang f)

-- decidability of inclusion in language ---------------------------------------
-- this follows from the decidability of equality on variables
∈-L-dec : (a : Var) → (l : Lang) → (a ∈-L l) ⊎ ((a ∈-L l) → Ø)
∈-L-dec a [] = inr λ ()
∈-L-dec a (x ∷ xs) with a ≡Var? x
... | yes a≡x = inl (inl a≡x)
... | no  a≢x with ∈-L-dec a xs
∈-L-dec a (x ∷ xs) | no a≢x | inl a∈xs = inl (inr a∈xs)
∈-L-dec a (x ∷ xs) | no a≢x | inr a∉xs = inr [ a≢x , a∉xs ]

-- equivalence ∈-F and ∈-L -----------------------------------------------------
-- i.e. a is in a formula f iff a is in the language of f
∈-F-to-∈-L : (f : F) → (a : Var) → (a ∈-F f) → (a ∈-L (lang-of f))
-- this direction is essentially the definition of the language of a formula
∈-F-to-∈-L f a a∈f = a∈lf
  where
    lf = p1 (lang f)
    lf-is-lang-of-f = p2 (lang f)

    a∈lf : a ∈-L lf
    a∈lf = lf-is-lang-of-f a a∈f

∈-L-to-∈-F : (f : F) → (a : Var) → (a ∈-L (lang-of f)) → (a ∈-F f)
∈-L-to-∈-F (V x) a (inl a∈x) = a∈x
∈-L-to-∈-F (f ∧ g) a a∈lf∧g with ∪-L-∈ (lang-of f) (lang-of g) a a∈lf∧g
... | inl a∈lf = inl (∈-L-to-∈-F f a a∈lf)
... | inr a∈lg = inr (∈-L-to-∈-F g a a∈lg)
∈-L-to-∈-F (f ∨ g) a a∈lf∨g with ∪-L-∈ (lang-of f) (lang-of g) a a∈lf∨g
... | inl a∈lf = inl (∈-L-to-∈-F f a a∈lf)
... | inr a∈lg = inr (∈-L-to-∈-F g a a∈lg)
∈-L-to-∈-F (f ⇒ g) a a∈lf⇒g with ∪-L-∈ (lang-of f) (lang-of g) a a∈lf⇒g
... | inl a∈lf = inl (∈-L-to-∈-F f a a∈lf)
... | inr a∈lg = inr (∈-L-to-∈-F g a a∈lg)

-- increasing formula increases language ---------------------------------------
-- i.e. if a is in the language of f then a also in language of f ∘ g
-- where ∘ ∈ {∧, ∨, ⇒}
-- the same holds when a is in the language of g
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
