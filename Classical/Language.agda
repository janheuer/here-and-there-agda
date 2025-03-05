module Classical.Language where

open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Agda.Builtin.Unit using (tt)
open import Data.Bool renaming (Bool to 𝔹) using (false)
open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Data.Product renaming (proj₁ to p1 ; proj₂ to p2) using (_×_ ; _,_ ; Σ-syntax)
open import Data.Sum renaming (inj₁ to inl ; inj₂ to inr) using (_⊎_ ; [_,_])
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim) using ()

open import Classical.Base

_on-lang_ : (i : IPC) → (l : List Var) → Σ[ j ∈ IPC ] ((a : Var) → ((a ∈-L l) → (j a ≡ i a)) × (((a ∈-L l) → Ø) → (j a ≡ false)))
i on-lang l = j , proof
  where
    j : IPC
    j a with ∈-L-dec a l
    ... | inl a∈l = i a
    ... | inr a∉l = false

    a∈l-imp-ja≡ia : (a : Var) → a ∈-L l → j a ≡ i a
    a∈l-imp-ja≡ia a a∈l with ∈-L-dec a l
    ... | inl _ = refl
    ... | inr a∉l = Ø-elim (a∉l a∈l)

    a∉l-imp-ja≡false : (a : Var) → (a ∈-L l → Ø) → j a ≡ false
    a∉l-imp-ja≡false a a∉l with ∈-L-dec a l
    ... | inl a∈l = Ø-elim (a∉l a∈l)
    ... | inr _ = refl

    proof = λ a → a∈l-imp-ja≡ia a , a∉l-imp-ja≡false a

_on-lang-of_ : IPC → F → IPC
i on-lang-of f = p1 (i on-lang (lang-of f))

on-lang-preserves-⊧C : (f : F) → (i : IPC) → (i ⊧C f) → (i on-lang-of f) ⊧C f
on-lang-preserves-⊧C (V a) i ia≡true = ja≡true
  where
    la = p1 (lang (V a))
    la-is-lang-of-a = p2 (lang (V a))

    a∈la : a ∈-L la
    a∈la = la-is-lang-of-a a refl

    j = p1 (i on-lang la)
    j≡i-on-la = p2 (i on-lang la)

    ja≡ia : j a ≡ i a
    ja≡ia = p1 (j≡i-on-la a) a∈la

    ja≡true = trans ja≡ia ia≡true
      where
        trans : {a b c : 𝔹} → a ≡ b → b ≡ c → a ≡ c
        trans refl refl = refl
on-lang-preserves-⊧C (f ∧ g) i (i⊧f , i⊧g) = j⊧f∧g
   where
     l = p1 (lang (f ∧ g))
     l-is-lang-of-f∧g = p2 (lang (f ∧ g))

     j = p1 (i on-lang l)

     j⊧f : j ⊧C f
     j⊧f = {!!}

     j⊧g : j ⊧C g
     j⊧g = {!!}

     j⊧f∧g = j⊧f , j⊧g
on-lang-preserves-⊧C (f ∨ g) i (inl i⊧f) = {!!}
on-lang-preserves-⊧C (f ∨ g) i (inr i⊧g) = {!!}
on-lang-preserves-⊧C (f ⇒ g) i = {!!}
