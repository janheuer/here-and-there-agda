module Equilibrium.Base where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product renaming (proj₁ to p1 ; proj₂ to p2) using (_×_ ; _,_)
open import Data.Sum renaming (inj₁ to inl ; inj₂ to inr) using ()
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim) using ()

open import Formula public
open import Classical public
open import HereAndThere public

-- definition of equilibrium models --------------------------------------------
-- def: h minimal model
-- the total model <t,t> is minimal in the here component for the formula f
min-h : (t : IPC) → (f : F) → Set
min-h t f = (h : IPC) → (p : h ⊆ t) → ((IHT h t p) ⊧HT f) → h ≡ t

-- def: equilibrium model
-- the total model <t,t> is an ht model of ϕ
-- and t is minimal in the here component
_⊧EQ_ : IPC → F → Set
t ⊧EQ ϕ = ((THT t) ⊧HT ϕ) × (min-h t ϕ)

-- def: equivalence under equilibrium model
-- the formulas f and g have the same equilibrium models
_≡EQ_ : F → F → Set
f ≡EQ g = (i : IPC) → (i ⊧EQ f → i ⊧EQ g) × (i ⊧EQ g → i ⊧EQ f)

-- thm: symmetry of equivalence under equilibrium model
symm≡EQ : {f g : F} → (f ≡EQ g) → (g ≡EQ f)
symm≡EQ {f} {g} f≡EQg i = (p2 (f≡EQg i)) ,
                          (p1 (f≡EQg i))

-- def: strong equivalence
-- the formulas f and g have the same models in conjunction with any formula h
_≡SEQ_ : F → F → Set
f ≡SEQ g = (h : F) → (f ∧ h) ≡EQ (g ∧ h)

-- thm: symmetry of strong equivalence
symm≡SEQ : {f g : F} → (f ≡SEQ g) → (g ≡SEQ f)
symm≡SEQ {f} {g} f≡SEQg h = symm≡EQ {f ∧ h} {g ∧ h} (f≡SEQg h)

-- theorems relating strong equivalence and ht equivalence ---------------------
-- thm: ht equivalence implies equivalence under equilibrium models
≡HT→≡EQ : {f g : F} → f ≡HT g → f ≡EQ g
≡HT→≡EQ {f} {g} f≡HTg i = EQf→EQg , EQg→EQf
  where
    _×→_ : {A B C D : Set} → (A → C) → (B → D) → (A × B) → (C × D)
    f ×→ g = λ (a , b) → f a , g b

    -- extracting f ⇒ g
    i⊧f⇒g : ((THT i) ⊧HT f) → ((THT i) ⊧HT g)
    i⊧f⇒g = p1 (p1 (f≡HTg (THT i)))

    -- extracting g ⇒ f
    i⊧g⇒f : ((THT i) ⊧HT g) → ((THT i) ⊧HT f)
    i⊧g⇒f = p1 (p2 (f≡HTg (THT i)))

    -- if <i,i> is h-minimal for f it is also for g
    min-i-g : (min-h i f) → (min-h i g)
    min-i-g min-i-f h p hi⊧g =
      let
        hi⊧f = (p1 (p2 (f≡HTg (IHT h i p))) hi⊧g)
      in
        min-i-f h p hi⊧f

    -- if <i,i> is h-minimal for g it is also for f
    min-i-f : (min-h i g) → (min-h i f)
    min-i-f min-i-g h p hi⊧f =
      let
        hi⊧g = (p1 (p1 (f≡HTg (IHT h i p))) hi⊧f)
      in
        min-i-g h p hi⊧g

    EQf→EQg : i ⊧EQ f → i ⊧EQ g
    EQf→EQg = i⊧f⇒g ×→ min-i-g

    EQg→EQf : i ⊧EQ g → i ⊧EQ f
    EQg→EQf = i⊧g⇒f ×→ min-i-f

-- thm: ht equivalence implies strong equivalence
≡HT→≡SEQ : {f g : F} → f ≡HT g → f ≡SEQ g
≡HT→≡SEQ {f} {g} f≡HTg h =
  let
    f∧h≡HTg∧h = f ∧ h ≡HT⟨ replace∧lhs f≡HTg ⟩
                g ∧ h ■
  in
    ≡HT→≡EQ f∧h≡HTg∧h

-- incomplete ------------------------------------------------------------------
-- helper theorems 1-3 for ≡SEQ→≡HT
-- 1) not ht equivalent implies not strongly equivalent
-- ≢HT→≢SEQ : {f g : F} → (f ≡HT g → Ø) → (f ≡SEQ g → Ø)
-- ≢HT→≢SEQ {f} {g} f≢HTg = {!!}

-- 2) if <H,T> ⊧ f and <H,T> ⊭ g then f ≢HT g
i⊧HTf×i⊭g→i≢HTg : {f g : F} → {i : IPHT} → (i ⊧HT f) → (i ⊧HT g → Ø) → (f ≡HT g → Ø)
i⊧HTf×i⊭g→i≢HTg {f} {g} {i} i⊧f i⊭g f≡g =
  let
    ((i⊧f⇒g , _) , _) = f≡g i
    i⊧g = i⊧f⇒g i⊧f
    f≢g = Ø-elim (i⊭g i⊧g)
  in
    f≢g

-- 3) if f ≡SEQ g and <H,T> ⊧ f then <H,T> ⊧ g
-- f≡SEQg×i⊧HTf→i⊧HTg : {f g : F} → f ≡SEQ g → {i : IPHT} → (i ⊧HT f) → (i ⊧HT g)
-- f≡SEQg×i⊧HTf→i⊧HTg {f} {g} f≡SEQg {i} i⊧HTf with dec-HT g i
-- ... | inl i⊧HTg = i⊧HTg
-- ... | inr i⊭HTg =
--   let
--     f≢HTg =  i⊧HTf×i⊭g→i≢HTg i⊧HTf i⊭HTg
--     f≢SEQg = ≢HT→≢SEQ {f} {g} f≢HTg
--     contra = f≢SEQg f≡SEQg
--     i⊧HTg = Ø-elim contra
--   in
--     i⊧HTg

-- thm: strong equivalence implies ht equivalence
-- ≡SEQ→≡HT : {f g : F} → f ≡SEQ g → f ≡HT g
-- ≡SEQ→≡HT {f} {g} f≡SEQg i@(IHT h t p) =
--   let
--     i⊧f⇒g = (λ i⊧HTf → f≡SEQg×i⊧HTf→i⊧HTg f≡SEQg i⊧HTf) ,
--              λ t⊧Cf → total-ht-to-c (f≡SEQg×i⊧HTf→i⊧HTg f≡SEQg (total-c-to-ht t⊧Cf))
--     g≡SEQf = symm≡SEQ f≡SEQg
--     i⊧g⇒f = (λ i⊧HTg → f≡SEQg×i⊧HTf→i⊧HTg g≡SEQf i⊧HTg) ,
--              λ t⊧Cg → total-ht-to-c (f≡SEQg×i⊧HTf→i⊧HTg g≡SEQf (total-c-to-ht t⊧Cg))
--   in
--     i⊧f⇒g , i⊧g⇒f
--------------------------------------------------------------------------------
