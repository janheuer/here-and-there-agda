module Equilibrium.Base where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product renaming (proj₁ to p1 ; proj₂ to p2) using (_×_ ; _,_)

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

