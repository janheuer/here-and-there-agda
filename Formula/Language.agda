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

-- first we define the language of a formula
_∈-F_ : Var → F → Set
a ∈-F ⊥ = Ø
a ∈-F V x = a ≡ x
a ∈-F (f ∧ g) = (a ∈-F f) ⊎ (a ∈-F g)
a ∈-F (f ∨ g) = (a ∈-F f) ⊎ (a ∈-F g)
a ∈-F (f ⇒ g) = (a ∈-F f) ⊎ (a ∈-F g)

_∈-L_ : Var → List Var → Set
a ∈-L [] = Ø
a ∈-L (x ∷ l) = (a ≡ x) ⊎ (a ∈-L l)

∈-L-++ : (l1 l2 : List Var) → (a : Var) → ((a ∈-L l1) ⊎ (a ∈-L l2)) → a ∈-L (l1 ++ l2)
∈-L-++ [] l2 a (inr a∈l2) = a∈l2
∈-L-++ (x ∷ l1) [] a (inl (inl a≡x)) = inl a≡x
∈-L-++ (x ∷ l1) [] a (inl (inr a∈l1)) = inr (∈-L-++ l1 [] a (inl a∈l1))
∈-L-++ (x1 ∷ l1) (x2 ∷ l2) a (inl (inl a≡x1)) = inl a≡x1
∈-L-++ (x1 ∷ l1) (x2 ∷ l2) a (inl (inr a∈l1)) = inr (∈-L-++ l1 (x2 ∷ l2) a (inl a∈l1))
∈-L-++ (x1 ∷ l1) (x2 ∷ l2) a (inr a∈x2∷l2) = inr (∈-L-++ l1 (x2 ∷ l2) a (inr a∈x2∷l2))

_is-lang-of_ : (l : List Var) → (f : F) → Set
l is-lang-of f = (a : Var) → (a ∈-F f) → (a ∈-L l)

lang : (f : F) → Σ[ l ∈ List Var ] (l is-lang-of f)
lang ⊥ = [] , λ a a∈⊥ → a∈⊥
lang (V a) = (a ∷ []) , λ b b≡a → inl b≡a
lang (f ∧ g) = l , l-is-lang-of-f∧g
  where
    lf = p1 (lang f)
    lf-is-lang-of-f = p2 (lang f)

    lg = p1 (lang g)
    lg-is-lang-of-g = p2 (lang g)

    l = lf ++ lg
    l-is-lang-of-f∧g : l is-lang-of (f ∧ g)
    l-is-lang-of-f∧g a (inl a∈f) = ∈-L-++ lf lg a (inl (lf-is-lang-of-f a a∈f))
    l-is-lang-of-f∧g a (inr a∈g) = ∈-L-++ lf lg a (inr (lg-is-lang-of-g a a∈g))
lang (f ∨ g) = l , l-is-lang-of-f∧g
  where
    lf = p1 (lang f)
    lf-is-lang-of-f = p2 (lang f)

    lg = p1 (lang g)
    lg-is-lang-of-g = p2 (lang g)

    l = lf ++ lg
    l-is-lang-of-f∧g : l is-lang-of (f ∧ g)
    l-is-lang-of-f∧g a (inl a∈f) = ∈-L-++ lf lg a (inl (lf-is-lang-of-f a a∈f))
    l-is-lang-of-f∧g a (inr a∈g) = ∈-L-++ lf lg a (inr (lg-is-lang-of-g a a∈g))
lang (f ⇒ g) = l , l-is-lang-of-f∧g
  where
    lf = p1 (lang f)
    lf-is-lang-of-f = p2 (lang f)

    lg = p1 (lang g)
    lg-is-lang-of-g = p2 (lang g)

    l = lf ++ lg
    l-is-lang-of-f∧g : l is-lang-of (f ∧ g)
    l-is-lang-of-f∧g a (inl a∈f) = ∈-L-++ lf lg a (inl (lf-is-lang-of-f a a∈f))
    l-is-lang-of-f∧g a (inr a∈g) = ∈-L-++ lf lg a (inr (lg-is-lang-of-g a a∈g))

lang-of : F → List Var
lang-of f = p1 (lang f)

-- TODO: update to Dec type
∈-L-dec : (a : Var) → (l : List Var) → (a ∈-L l) ⊎ ((a ∈-L l) → Ø)
∈-L-dec a [] = inr λ ()
∈-L-dec a (x ∷ xs) with a ≡Var? x
... | yes a≡x = inl (inl a≡x)
... | no  a≢x with ∈-L-dec a xs
∈-L-dec a (x ∷ xs) | no a≢x | inl a∈xs = inl (inr a∈xs)
∈-L-dec a (x ∷ xs) | no a≢x | inr a∉xs = inr [ a≢x , a∉xs ]

-- language increases with increasing the formula
∈-F-∧ : (f g : F) → (a : Var) → (a ∈-F f) → (a ∈-F (f ∧ g))
∈-F-∧ f g a a∈f = inl a∈f

∈-F-to-∈-L : (f : F) → (a : Var) → (a ∈-F f) → (a ∈-L (lang-of f))
∈-F-to-∈-L f a a∈f = a∈lf
  where
    lf = p1 (lang f)
    lf-is-lang-of-f = p2 (lang f)

    a∈lf : a ∈-L lf
    a∈lf = lf-is-lang-of-f a a∈f

