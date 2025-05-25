module HereAndThere.LogicPrograms.DoubleNegation where

-- converting a logic program of the form
-- SC ⇒ SD
-- to a logic program of the form
-- Body ⇒ Head
-- where Body/Head are conjunctions/disjunctions of
-- ⊤/⊥, V a, ¬ V a, ¬¬ V a
-- i.e., we need to remove ⊥ from SC,
--       and remove ⊤ from SD

open import Data.Product using (_×_ ; _,_ ; <_,_> ; Σ-syntax)
                         renaming (proj₁ to p1 ; proj₂ to p2)
open import Data.Sum using (_⊎_ ; [_,_]) renaming (inj₁ to inl ; inj₂ to inr)
open import Data.Empty renaming (⊥ to Ø) using ()
open import Agda.Builtin.Unit renaming (⊤ to Unit) using (tt)
open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Data.Nat using (ℕ ; suc ; _+_)
open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Relation.Binary.PropositionalEquality.Core using (sym)
open import Data.Nat.Properties using (m+n≡0⇒m≡0 ; m+n≡0⇒n≡0)

open import HereAndThere.Base
open import HereAndThere.Equivalences
open import HereAndThere.LogicPrograms.Nested
open import HereAndThere.LogicPrograms.SimpleDisjunctiveConjunctive
open import Formula.LogicPrograms
open import Formula.LogicPrograms.Nested
open import Formula.LogicPrograms.DoubleNegation
open import Formula.LogicPrograms.DisjunctiveConjunctive
open import NatHelper

-- 1) helper functions to get the number of occurrences of ⊥/⊤ -----------------
-- 1.1) number of occurrences of ⊤ in a formula
∣_∣⊤ : F → ℕ
∣ ⊥ ∣⊤ = 0
∣ (⊥ ⇒ ⊥) ∣⊤ = 1
∣ V x ∣⊤ = 0
∣ f ∧ g ∣⊤ = ∣ f ∣⊤ + ∣ g ∣⊤
∣ f ∨ g ∣⊤ = ∣ f ∣⊤ + ∣ g ∣⊤
∣ f ⇒ g ∣⊤ = ∣ f ∣⊤ + ∣ g ∣⊤

-- alternate definition that also returns equality proof
∣_∣⊤×≡ : (f : F) → Σ[ n ∈ ℕ ] (n ≡ ∣ f ∣⊤)
∣ f ∣⊤×≡ = ∣ f ∣⊤ , refl

-- 1.2) number of occurrences of ⊥ in a formula
∣_∣⊥ : F → ℕ
∣ ⊥ ∣⊥ = 1
∣ (⊥ ⇒ ⊥) ∣⊥ = 0
∣ V x ∣⊥ = 0
∣ (V x) ⇒ ⊥ ∣⊥ = 0
∣ ((V x) ⇒ ⊥) ⇒ ⊥ ∣⊥ = 0
∣ f ∧ g ∣⊥ = ∣ f ∣⊥ + ∣ g ∣⊥
∣ f ∨ g ∣⊥ = ∣ f ∣⊥ + ∣ g ∣⊥
∣ f ⇒ g ∣⊥ = ∣ f ∣⊥ + ∣ g ∣⊥

-- alternate definition that also returns equality proof
∣_∣⊥×≡ : (f : F) → Σ[ n ∈ ℕ ] (n ≡ ∣ f ∣⊥)
∣ f ∣⊥×≡ = ∣ f ∣⊥ , refl

-- 1.3) specialisations of counting functions to simple conjunctive disjunctive
-- rules, note that they only count the occurrences that need to be removed,
-- i.e., ⊤ is only counted in the head, and ⊥ only in the body
∣_∣SCD⊤ : SCD → ℕ
∣ (b ⇒ h) , _ ∣SCD⊤ = ∣ h ∣⊤

∣_∣SCD⊥ : SCD → ℕ
∣ (b ⇒ h) , _ ∣SCD⊥ = ∣ b ∣⊥

-- 2) a simple disjunction containing ⊤ is equivalent to just ⊤ ----------------
sd⊤-eq-⊤ : (ϕ : F) → isSD ϕ → (n : ℕ) → suc n ≡ ∣ ϕ ∣⊤ → (ϕ ≡HT ⊤)
-- base case: sd is ⊤
sd⊤-eq-⊤ (⊥ ⇒ ⊥) tt 0 refl = refl⇔
-- step case: f∨g contains n+1 occurences of ⊤
-- we split into cases on the number of ⊤ in f
sd⊤-eq-⊤ (f ∨ g) (fp , gp) n sn≡∣f∨g∣⊤ with ∣ f ∣⊤×≡
-- A) f contains no ⊤
... | 0 , 0≡∣f∣⊤ = f∨g≡⊤
  where
    -- g contains n+1 occurrences of ⊤
    sn≡∣g∣⊤ = x≡y+z∧0≡y⇒x≡z sn≡∣f∨g∣⊤ 0≡∣f∣⊤
    -- g is equivalent to ⊤ by recursion
    g≡⊤ = sd⊤-eq-⊤ g gp n sn≡∣g∣⊤
    -- disjunction is also equivalent to ⊤
    f∨g≡⊤ = f ∨ g ≡HT⟨ replace∨rhs g≡⊤ ⟩
            f ∨ ⊤ ≡HT⟨ ⊤-rzero-∨ ⟩
            ⊤ ■
-- B) f contains m+1 occurrences of ⊤
... | suc m , sm≡∣f∣⊤ = f∨g≡⊤
  where
    -- f is equivalent to ⊤ by recursion
    f≡⊤ = sd⊤-eq-⊤ f fp m sm≡∣f∣⊤
    -- disjunction is then also equivalent to ⊤
    f∨g≡⊤ = f ∨ g ≡HT⟨ replace∨lhs f≡⊤ ⟩
            ⊤ ∨ g ≡HT⟨ ⊤-lzero-∨ ⟩
            ⊤ ■
-- absurd cases
sd⊤-eq-⊤ (V x ⇒ ⊥) ϕp n ()
sd⊤-eq-⊤ (V x ⇒ V x₁) ϕp n ()
sd⊤-eq-⊤ (V x ⇒ (ϕ' ∧ ϕ'')) () n p
sd⊤-eq-⊤ (V x ⇒ (ϕ' ∨ ϕ'')) () n p
sd⊤-eq-⊤ (V x ⇒ ⊥ ⇒ ⊥) () n p
sd⊤-eq-⊤ (V x ⇒ ⊥ ⇒ V x₁) () n p
sd⊤-eq-⊤ (V x ⇒ ⊥ ⇒ (ϕ'' ∧ ϕ''')) () n p
sd⊤-eq-⊤ (V x ⇒ ⊥ ⇒ (ϕ'' ∨ ϕ''')) () n p
sd⊤-eq-⊤ (V x ⇒ ⊥ ⇒ ϕ'' ⇒ ϕ''') () n p
sd⊤-eq-⊤ (V x ⇒ V x₁ ⇒ ϕ'') () n p
sd⊤-eq-⊤ (V x ⇒ (ϕ' ∧ ϕ''') ⇒ ϕ'') () n p
sd⊤-eq-⊤ (V x ⇒ (ϕ' ∨ ϕ''') ⇒ ϕ'') () n p
sd⊤-eq-⊤ (V x ⇒ (ϕ' ⇒ ϕ''') ⇒ ϕ'') () n p
sd⊤-eq-⊤ ((V x ⇒ ⊥) ⇒ ⊥) ϕp n ()
sd⊤-eq-⊤ ((V x ⇒ ⊥) ⇒ V x₁) () n p
sd⊤-eq-⊤ ((V x ⇒ ⊥) ⇒ (ϕ' ∧ ϕ'')) () n p
sd⊤-eq-⊤ ((V x ⇒ ⊥) ⇒ (ϕ' ∨ ϕ'')) () n p
sd⊤-eq-⊤ ((V x ⇒ ⊥) ⇒ ϕ' ⇒ ϕ'') () n p

-- 3) a simple cojunction containing ⊥ is equivalent to just ⊥ -----------------
sc⊥-eq-⊥ : (ϕ : F) → isSC ϕ → (n : ℕ) → suc n ≡ ∣ ϕ ∣⊥ → (ϕ ≡HT ⊥)
-- base case: sc is ⊥
sc⊥-eq-⊥ ⊥ tt 0 refl = refl⇔
-- step case: f∧g contains n+1 occurrences of ⊥
-- we split into cases on the number of ⊥ in f
sc⊥-eq-⊥ (f ∧ g) (fp , gp) n sn≡∣f∧g∣⊥ with ∣ f ∣⊥×≡
-- A) f contains no ⊥
... | 0 , 0≡∣f∣⊥ = f∧g≡⊥
  where
    -- g contains n+1 occurrences of ⊥
    sn≡∣g∣⊥ = x≡y+z∧0≡y⇒x≡z sn≡∣f∧g∣⊥ 0≡∣f∣⊥
    -- g is equivalent to ⊥ by recursion
    g≡⊥ = sc⊥-eq-⊥ g gp n sn≡∣g∣⊥
    -- conjunction is also equivalent to ⊥
    f∧g≡⊥ = f ∧ g ≡HT⟨ replace∧rhs g≡⊥ ⟩
            f ∧ ⊥ ≡HT⟨ ⊥-rzero-∧ ⟩
            ⊥ ■
-- B) f contains m+1 occurences of ⊥
... | suc m , sm≡∣f∣⊥ = f∧g≡⊥
  where
    -- f is equivalent to ⊥ by recursion
    f≡⊥ = sc⊥-eq-⊥ f fp m sm≡∣f∣⊥
    -- conjunction is also equivalent to ⊥
    f∧g≡⊥ = f ∧ g ≡HT⟨ replace∧lhs f≡⊥ ⟩
            ⊥ ∧ g ≡HT⟨ ⊥-lzero-∧ ⟩
            ⊥ ■
-- absurd cases
sc⊥-eq-⊥ (⊥ ⇒ ⊥) tt 0 ()
sc⊥-eq-⊥ (⊥ ⇒ ⊥) tt (suc n) ()
sc⊥-eq-⊥ (V x ⇒ ⊥) fp n ()
sc⊥-eq-⊥ ((V x ⇒ ⊥) ⇒ ⊥) fp n ()
sc⊥-eq-⊥ ((V x ⇒ ⊥) ⇒ V x₁) () n p
sc⊥-eq-⊥ ((V x ⇒ ⊥) ⇒ (f ∧ f₁)) () n p
sc⊥-eq-⊥ ((V x ⇒ ⊥) ⇒ (f ∨ f₁)) () n p
sc⊥-eq-⊥ ((V x ⇒ ⊥) ⇒ f ⇒ f₁) () n p

-- 4) a simple conjunctive disjunctive rule that contains ⊤ in the head --------
--    is equivalent to just ⊤ --------------------------------------------------
⇒⊤-eq-⊤ : ((ϕ , ϕp) : SCD) → (n : ℕ) → (suc n ≡ ∣ (ϕ , ϕp) ∣SCD⊤) → (ϕ ≡HT ⊤)
⇒⊤-eq-⊤ (f ⇒ g , (fp , gp)) n p =
  let
    g≡⊤ = sd⊤-eq-⊤ g gp n p
    f⇒g≡⊤ = f ⇒ g ≡HT⟨ replace⇒rhs g≡⊤ ⟩
             f ⇒ ⊤ ≡HT⟨ ⊤-rzero-⇒ ⟩
             ⊤ ■
  in
    f⇒g≡⊤

-- 4) a simple conjunctive disjunctive rule that contains ⊥ in the body --------
--    is equivalent to just ⊤ --------------------------------------------------
⊥⇒-eq-⊤ : ((ϕ , ϕp) : SCD) → (n : ℕ) → (suc n ≡ ∣ (ϕ , ϕp) ∣SCD⊥) → (ϕ ≡HT ⊤)
⊥⇒-eq-⊤ (f ⇒ g , (fp , gp)) n p =
  let
    f≡⊥ = sc⊥-eq-⊥ f fp n p
    f⇒g≡⊥ = f ⇒ g ≡HT⟨ replace⇒lhs f≡⊥ ⟩
             ⊥ ⇒ g ≡HT⟨ ⊥-lzero-⇒ ⟩
             ⊤ ■
  in
    f⇒g≡⊥

-- 5) direct conversion of simple conjunctions/disjunctions to body/head -------
--    expression with double negation ------------------------------------------
sc-without-⊥-isBE2¬ : ((ϕ , _) : SC) → (0 ≡ ∣ ϕ ∣⊥) → isBE2¬ ϕ
-- base cases: isBE2¬ is the Unit type
sc-without-⊥-isBE2¬ (V x , tt) p = tt
sc-without-⊥-isBE2¬ (V x ⇒ ⊥ , tt) p = tt
sc-without-⊥-isBE2¬ ((V x ⇒ ⊥) ⇒ ⊥ , tt) p = tt
sc-without-⊥-isBE2¬ (⊥ ⇒ ⊥ , tt) p = tt
-- step case: conversion of subformulas
sc-without-⊥-isBE2¬ (f ∧ g , (fp , gp)) 0≡∣f∧g∣⊥ =
  let
    0≡∣f∣⊥ = sym (m+n≡0⇒m≡0 (∣ f ∣⊥) {∣ g ∣⊥} (sym 0≡∣f∧g∣⊥))
    0≡∣g∣⊥ = sym (m+n≡0⇒n≡0 (∣ f ∣⊥) {∣ g ∣⊥} (sym 0≡∣f∧g∣⊥))
  in
    sc-without-⊥-isBE2¬ (f , fp) 0≡∣f∣⊥ , sc-without-⊥-isBE2¬ (g , gp) 0≡∣g∣⊥
-- absurd cases
sc-without-⊥-isBE2¬ (V x ⇒ V x₁ , ()) p
sc-without-⊥-isBE2¬ (V x ⇒ (f ∧ f₁) , ()) p
sc-without-⊥-isBE2¬ (V x ⇒ (f ∨ f₁) , ()) p
sc-without-⊥-isBE2¬ (V x ⇒ f ⇒ f₁ , ()) p
sc-without-⊥-isBE2¬ ((V x ⇒ V x₁) ⇒ f₁ , ()) p
sc-without-⊥-isBE2¬ ((V x ⇒ (f ∧ f₂)) ⇒ f₁ , ()) p
sc-without-⊥-isBE2¬ ((V x ⇒ (f ∨ f₂)) ⇒ f₁ , ()) p
sc-without-⊥-isBE2¬ ((V x ⇒ f ⇒ f₂) ⇒ f₁ , ()) p

sd-without-⊤-isHE2¬ : ((ϕ , _) : SD) → (0 ≡ ∣ ϕ ∣⊤) → isHE2¬ ϕ
-- base cases: isHE2¬ is the Unit type
sd-without-⊤-isHE2¬ (⊥ , fp) p = tt
sd-without-⊤-isHE2¬ (V x , fp) p = tt
sd-without-⊤-isHE2¬ (V x ⇒ ⊥ , tt) refl = tt
sd-without-⊤-isHE2¬ ((V x ⇒ ⊥) ⇒ ⊥ , tt) refl = tt
-- step case: conversion of subformulas
sd-without-⊤-isHE2¬ (f ∨ g , (fp , gp)) 0≡∣f∨g∣⊤ =
  let
    0≡∣f∣⊤ = sym (m+n≡0⇒m≡0 (∣ f ∣⊤) {∣ g ∣⊤} (sym 0≡∣f∨g∣⊤))
    0≡∣g∣⊤ = sym (m+n≡0⇒n≡0 (∣ f ∣⊤) {∣ g ∣⊤} (sym 0≡∣f∨g∣⊤))
  in
    sd-without-⊤-isHE2¬ (f , fp) 0≡∣f∣⊤ , sd-without-⊤-isHE2¬ (g , gp) 0≡∣g∣⊤
-- absurd cases
sd-without-⊤-isHE2¬ (⊥ ⇒ ⊥ , tt) ()
sd-without-⊤-isHE2¬ (⊥ ⇒ V x , ()) p
sd-without-⊤-isHE2¬ (⊥ ⇒ (f ∧ f₁) , ()) p
sd-without-⊤-isHE2¬ (⊥ ⇒ (f ∨ f₁) , ()) p
sd-without-⊤-isHE2¬ (⊥ ⇒ f ⇒ f₁ , ()) p

-- 6) conversion of simple conjunctive disjunctive logic programs to logic -----
--    programs with double negation --------------------------------------------

-- first, conversion of rules
scd-eq-lp2¬ : ((ϕ , ϕp) : SCD)
              → (n : ℕ) → (n ≡ ∣ (ϕ , ϕp) ∣SCD⊥)
              → (m : ℕ) → (m ≡ ∣ (ϕ , ϕp) ∣SCD⊤)
              → Σ[ (Π , _) ∈ LP2¬ ] (ϕ ≡HT Th2F Π)
-- case 1: no occurences of ⊥/⊤ in body/head
scd-eq-lp2¬ (f ⇒ g , (fp , gp)) 0 0≡∣f∣⊥ 0 0≡∣g∣⊤ = (Π , Πp) , f⇒g≡Π
  where
    -- direct conversion of f and g
    fisBE2¬ = sc-without-⊥-isBE2¬ (f , fp) 0≡∣f∣⊥
    gisHE2¬ = sd-without-⊤-isHE2¬ (g , gp) 0≡∣g∣⊤

    ϕ = f ⇒ g
    ϕp : isR2¬ ϕ
    ϕp = fisBE2¬ , gisHE2¬

    Π = ϕ ∷ []
    Πp : isLP2¬ Π
    Πp = ϕp , tt

    f⇒g≡Π = f ⇒ g               ≡HT⟨ ⊤-rid-∧ ⟩ˢ
             (f ⇒ g) ∧ ⊤         ≡HT⟨def⟩
             Th2F ((f ⇒ g) ∷ []) ■
-- case 2: the head has m+1 occurences of ⊤
scd-eq-lp2¬ (f ⇒ g , (fp , gp)) 0 0≡∣f∣⊥ (suc m) sm≡∣g∣⊤ =
  let
    -- then f⇒g is equivalent to ⊤, which is the empty program
    f⇒g≡⊤ = ⇒⊤-eq-⊤ (f ⇒ g , (fp , gp)) m sm≡∣g∣⊤
  in
    ([] , tt) , f⇒g≡⊤
-- case 3: the body has n+1 occurrences of ⊥
scd-eq-lp2¬ (f ⇒ g , fp , gp) (suc n) sn≡∣f∣⊥ _ _ =
  let
    -- then f⇒g is equivaltn to ⊤, which is the empty program
    f⇒g≡⊤ = ⊥⇒-eq-⊤ (f ⇒ g , (fp , gp)) n sn≡∣f∣⊥
  in
    ([] , tt) , f⇒g≡⊤

-- next, mutliple logic programs with double negation can be combined
LP2¬++LP2¬isLP2¬ : ((Γ1 , _) (Γ2 , _) : LP2¬) → isLP2¬ (Γ1 ++ Γ2)
LP2¬++LP2¬isLP2¬ ([] , tt) (Γ , Γp) = Γp
LP2¬++LP2¬isLP2¬ (ϕ ∷ Γ1 , (ϕp , Γ1p)) (Γ2 , Γ2p) = ϕp , LP2¬++LP2¬isLP2¬ (Γ1 , Γ1p) (Γ2 , Γ2p)

-- finally, conversion of simple cojunctive disjunctive logic programs
scdlp-eq-lp2¬ : ((Γ , _) : SCDLP) → Σ[ (Π , _) ∈ LP2¬ ] (Th2F Γ ≡HT Th2F Π)
-- base case: empty program
scdlp-eq-lp2¬ ([] , tt) = ([] , tt) , refl⇔
-- step case
scdlp-eq-lp2¬ (ϕ ∷ Γ , (ϕp , Γp)) =
  let
    -- first, conversion of ϕ to Π1 (a logic program with double negation)
    ((Π1 , Π1p) , ϕ≡Π1) = scd-eq-lp2¬ (ϕ , ϕp) ∣ ϕ , ϕp ∣SCD⊥ refl ∣ ϕ , ϕp ∣SCD⊤ refl
    -- second, conversion of Γ to Π2 (a logic program with double negation)
    ((Π2 , Π2p) , Γ≡Π2) = scdlp-eq-lp2¬ (Γ , Γp)
    -- then, we combine Π1 and Π2 to Π
    Π = Π1 ++ Π2
    Πp = LP2¬++LP2¬isLP2¬ (Π1 , Π1p) (Π2 , Π2p)
    -- finally, ϕ∷Γ is equivalent to Π
    ϕ∷Γ≡Π = Th2F (ϕ ∷ Γ)       ≡HT⟨def⟩
             ϕ ∧ Th2F Γ         ≡HT⟨ replace∧lhs ϕ≡Π1 ⟩
             Th2F Π1 ∧ Th2F Γ  ≡HT⟨ replace∧rhs Γ≡Π2 ⟩
             Th2F Π1 ∧ Th2F Π2 ≡HT⟨ Th∧Th-eq-Th++Th ⟩
             Th2F Π ■
  in
    (Π , Πp) , ϕ∷Γ≡Π
