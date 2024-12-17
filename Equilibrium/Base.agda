module Equilibrium.Base where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product renaming (proj₁ to p1 ; proj₂ to p2) using (_×_ ; _,_)
open import Data.Sum renaming (inj₁ to inl ; inj₂ to inr) using ()
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim) using ()

open import Formula public
open import Classical public
open import HereAndThere public

-- def: h minimal model
--      the total model <t,t> is minimal in the here component for the formula f
min-h : (t : IPC) → (f : F) → Set
min-h t f = (h : IPC) → (p : h ⊆ t) → ((IHT h t p) ⊧HT f) → h ≡ t

-- def: equilibrium model
--      the total model <t,t> is an ht model of ϕ
--      and t is minimal in the here component
_⊧EQ_ : IPC → F → Set
t ⊧EQ ϕ = ((THT t) ⊧HT ϕ) × (min-h t ϕ)

-- def: equivalence under equilibrium model
--      the formulas f and g have the same equilibrium models
_≡EQ_ : F → F → Set
f ≡EQ g = (i : IPC) → (i ⊧EQ f → i ⊧EQ g) × (i ⊧EQ g → i ⊧EQ f)

-- def: strong equivalence
--      the formulas f and g have the same models in conjunction with any formula h
_≡SEQ_ : F → F → Set
f ≡SEQ g = (h : F) → (f ∧ h) ≡EQ (g ∧ h)

-- thm: ht equivalence implies equivalence under equilibrium models
≡HT→≡EQ : {f g : F} → f ≡HT g → f ≡EQ g
≡HT→≡EQ {f} {g} f≡HTg i = EQf→EQg , EQg→EQf
  where
    _×→_ : {A B C D : Set} → (A → C) → (B → D) → (A × B) → (C × D)
    f ×→ g = λ (a , b) → f a , g b

    i⊧HTg : ((THT i) ⊧HT f) → ((THT i) ⊧HT g)
    i⊧HTg i⊧HTf = p1 (p1 (f≡HTg (THT i))) i⊧HTf

    i⊧HTf : ((THT i) ⊧HT g) → ((THT i) ⊧HT f)
    i⊧HTf i⊧HTg = p1 (p2 (f≡HTg (THT i))) i⊧HTg

    min-i-g : (min-h i f) → (min-h i g)
    min-i-g min-i-f h p hi⊧HTg =
      let
        hi⊧HTf = (p1 (p2 (f≡HTg (IHT h i p))) hi⊧HTg)
      in
        min-i-f h p hi⊧HTf

    min-i-f : (min-h i g) → (min-h i f)
    min-i-f min-i-g h p hi⊧HTf =
      let
        hi⊧HTg = (p1 (p1 (f≡HTg (IHT h i p))) hi⊧HTf)
      in
        min-i-g h p hi⊧HTg

    EQf→EQg : i ⊧EQ f → i ⊧EQ g
    EQf→EQg = i⊧HTg ×→ min-i-g

    EQg→EQf : i ⊧EQ g → i ⊧EQ f
    EQg→EQf = i⊧HTf ×→ min-i-f

-- thm: ht equivalence implies strong equivalence
≡HT→≡SEQ : {f g : F} → f ≡HT g → f ≡SEQ g
≡HT→≡SEQ {f} {g} f≡HTg h =
  let
    f∧h≡HTg∧h = f ∧ h ≡HT⟨ replace∧lhs f≡HTg ⟩
                g ∧ h ■
  in
    ≡HT→≡EQ f∧h≡HTg∧h
