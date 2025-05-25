module Equilibrium.StrongEquivalence where

-- definition of strong equivalence and proof that ht equivalence implies
-- strong equivalence

open import Data.Product renaming (proj₁ to p1 ; proj₂ to p2) using (_×_ ; _,_ ; map)
open import Data.Sum renaming (inj₁ to inl ; inj₂ to inr) using ()
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim) using ()

open import Equilibrium.Base

-- strong equivalence ----------------------------------------------------------
-- def: strong equivalence
-- the formulas f and g have the same models in conjunction with any formula h
_≡SEQ_ : F → F → Set
f ≡SEQ g = (h : F) → (f ∧ h) ≡EQ (g ∧ h)

-- thm: symmetry of strong equivalence
symm≡SEQ : {f g : F} → (f ≡SEQ g) → (g ≡SEQ f)
symm≡SEQ {f} {g} f≡SEQg h = symm≡EQ {f ∧ h} {g ∧ h} (f≡SEQg h)

-- theorems relating strong equivalence and ht equivalence ---------------------
-- 1) ht equivalence implies strong equivalence --------------------------------
-- thm: ht equivalence implies equivalence under equilibrium models
≡HT→≡EQ : {f g : F} → f ≡HT g → f ≡EQ g
≡HT→≡EQ {f} {g} f≡HTg t = EQf→EQg , EQg→EQf
  where
    -- extracting f ⇒ g
    t⊧f⇒g : ((THT t) ⊧HT f) → ((THT t) ⊧HT g)
    t⊧f⇒g = p1 (p1 (f≡HTg (THT t)))

    -- extracting g ⇒ f
    t⊧g⇒f : ((THT t) ⊧HT g) → ((THT t) ⊧HT f)
    t⊧g⇒f = p1 (p2 (f≡HTg (THT t)))

    -- if <t,t> is h-minimal for f it is also for g
    min-t-g : (min-h t f) → (min-h t g)
    min-t-g min-t-f h p ht⊧g =
      let
        -- <h,t> is a model of f extracted from equivalence of f and g
        ht⊧f = (p1 (p2 (f≡HTg (IHT h t p))) ht⊧g)
      in
        -- as <t,t> is minimal for f and <h,t> is a model of f we get h ≡ t
        min-t-f h p ht⊧f

    -- if <t,t> is h-minimal for g it is also for f
    min-t-f : (min-h t g) → (min-h t f)
    min-t-f min-t-g h p ht⊧f =
      let
        -- <h,t> is a model of g extracted from equivalence of f and g
        ht⊧g = (p1 (p1 (f≡HTg (IHT h t p))) ht⊧f)
      in
        -- as <t,t> is minimal for g and <h,t> is a model of g we get h ≡ t
        min-t-g h p ht⊧g

    -- combine proof parts, note that the ⊧EQ types are each pairs
    -- t⊧f⇒g converts the first proof component
    -- min-t-g converts the second proof component
    EQf→EQg : t ⊧EQ f → t ⊧EQ g
    EQf→EQg = map t⊧f⇒g min-t-g

    EQg→EQf : t ⊧EQ g → t ⊧EQ f
    EQg→EQf = map t⊧g⇒f min-t-f

-- thm: ht equivalence implies strong equivalence
≡HT→≡SEQ : {f g : F} → f ≡HT g → f ≡SEQ g
≡HT→≡SEQ {f} {g} f≡HTg h =
  let
    f∧h≡HTg∧h = f ∧ h ≡HT⟨ replace∧lhs f≡HTg ⟩
                g ∧ h ■
  in
    ≡HT→≡EQ f∧h≡HTg∧h

-- 2) strong equivalence implies ht equivalence --------------------------------
-- incomplete ------------------------------------------------------------------

-- the below code provides a first outline for proving that strong equivalence
-- implies ht equivalence
-- currently this is still incomplete as some more helper theorems are needed

-- helper theorems (A,B, and C) for ≡SEQ→≡HT
-- A) not ht equivalent implies not strongly equivalent
-- ≢HT→≢SEQ : {f g : F} → (f ≡HT g → Ø) → (f ≡SEQ g → Ø)
-- apadpting the proof form Lifschitz et al. 2001 requires more work on
-- converting interpretations to formulas
-- ≢HT→≢SEQ {f} {g} f≢HTg = {!!}

-- B) if <H,T> ⊧ f and <H,T> ⊭ g then f ≢HT g
i⊧HTf×i⊭g→i≢HTg : {f g : F} → {i : IPHT} → (i ⊧HT f) → (i ⊧HT g → Ø) → (f ≡HT g → Ø)
i⊧HTf×i⊭g→i≢HTg {f} {g} {i} i⊧f i⊭g f≡g =
  let
    ((i⊧f⇒g , _) , _) = f≡g i
    i⊧g = i⊧f⇒g i⊧f
    f≢g = Ø-elim (i⊭g i⊧g)
  in
    f≢g

-- C) if f ≡SEQ g and <H,T> ⊧ f then <H,T> ⊧ g
-- we keep the proof commented out as it uses A which is not proven
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
-- similar to C this proof is already complete but (indirectly) uses A
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
