module HereAndThere.LogicPrograms.SimpleDisjunctiveConjunctive where

-- every logic program of the form DNF ⇒ CNF is equivalent to a logic program
-- of the form SC ⇒ SD
-- the proof uses logic programs of the form DNF ⇒ SD as an intermediate form
-- i.e., 1) DNF ⇒ CNF to DNF ⇒ SD
--       2) DNF ⇒ SD  to SC  ⇒ SD
--       3) DNF ⇒ CNF to SC  ⇒ SD

open import Data.Product using (_×_ ; _,_ ; <_,_> ; Σ-syntax)
                         renaming (proj₁ to p1 ; proj₂ to p2)
open import Data.Sum using (_⊎_ ; [_,_]) renaming (inj₁ to inl ; inj₂ to inr)
open import Data.Empty renaming (⊥ to Ø) using ()
open import Agda.Builtin.Unit renaming (⊤ to Unit) using (tt)
open import Data.List using (List ; [] ; _∷_ ; _++_)

open import HereAndThere.Base
open import HereAndThere.Equivalences
open import HereAndThere.LogicPrograms.Nested
open import Formula.LogicPrograms
open import Formula.LogicPrograms.Nested
open import Formula.LogicPrograms.DoubleNegation
open import Formula.LogicPrograms.DisjunctiveConjunctive
open import FunctionHelper using ( restrict-sum     ; extract-product    ;
                                   restrict-sum-inl ; extract-product-p1 ;
                                   restrict-sum-inr ; extract-product-p2 )

-- 0) removal of disjunction/conjunctions in the bodies/heads of implications --
-- removal of disjunction in body of implications ------------------------------
-- (f ∨ g) ⇒ j is equivalent to (f ⇒ j) ∧ (g ⇒ j)
rem∨body : {f g j : F} → ((f ∨ g) ⇒ j) ≡HT ((f ⇒ j) ∧ (g ⇒ j))
rem∨body {f} {g} {j} i@(IHT h t p) =
  (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)
    where
      proof⇒C : t ⊧C ((f ∨ g) ⇒ j) → t ⊧C ((f ⇒ j) ∧ (g ⇒ j))
      -- (t ⊧C f∨g → t ⊧C j) → (t ⊧C f → t ⊧C j) × (t ⊧C g → t ⊧C j)
      proof⇒C = restrict-sum

      proof⇒HT : i ⊧HT ((f ∨ g) ⇒ j) → i ⊧HT ((f ⇒ j) ∧ (g ⇒ j))
      proof⇒HT (⊧HTf∨g⇒j , ⊧Cf∨g⇒j) =
        (restrict-sum-inl ⊧HTf∨g⇒j , (p1 (proof⇒C ⊧Cf∨g⇒j))) ,
        (restrict-sum-inr ⊧HTf∨g⇒j , (p2 (proof⇒C ⊧Cf∨g⇒j)))

      proof⇐C : t ⊧C ((f ⇒ j) ∧ (g ⇒ j)) → t ⊧C ((f ∨ g) ⇒ j)
      -- (t ⊧C f → t ⊧C j) × (t ⊧C g → t ⊧C j) → t ⊧C f∨g → t ⊧C j
      proof⇐C (⊧f⇒j , ⊧g⇒j) = [ ⊧f⇒j , ⊧g⇒j ]

      proof⇐HT : i ⊧HT ((f ⇒ j) ∧ (g ⇒ j)) → i ⊧HT ((f ∨ g) ⇒ j)
      proof⇐HT ((⊧HTf⇒j , ⊧Cf⇒j) , (⊧HTg⇒j , ⊧Cg⇒j)) =
        [ ⊧HTf⇒j , ⊧HTg⇒j ] ,
        proof⇐C (⊧Cf⇒j , ⊧Cg⇒j)

-- removal of conjucntion in head of implications ------------------------------
-- f ⇒ (g ∧ j) is equivalent to (f ⇒ g) ∧ (f ⇒ j)
rem∧head : {f g j : F} → (f ⇒ (g ∧ j)) ≡HT ((f ⇒ g) ∧ (f ⇒ j))
rem∧head {f} {g} {j} i@(IHT h t p) =
  (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)
    where
      proof⇒C : t ⊧C (f ⇒ (g ∧ j)) → t ⊧C ((f ⇒ g) ∧ (f ⇒ j))
      -- ((t ⊧C f) → (t ⊧C g × t ⊧C j)) → (t ⊧C f → t ⊧C g) × (t ⊧C f → t ⊧C j)
      proof⇒C = extract-product

      proof⇒HT : i ⊧HT (f ⇒ (g ∧ j)) → i ⊧HT ((f ⇒ g) ∧ (f ⇒ j))
      proof⇒HT (⊧HTf⇒g∧j , ⊧Cf⇒g∧j) =
        (extract-product-p1 ⊧HTf⇒g∧j , (p1 (proof⇒C ⊧Cf⇒g∧j))) ,
        (extract-product-p2 ⊧HTf⇒g∧j , (p2 (proof⇒C ⊧Cf⇒g∧j)))

      proof⇐C : t ⊧C ((f ⇒ g) ∧ (f ⇒ j)) → t ⊧C (f ⇒ (g ∧ j))
      -- (t ⊧C f → t ⊧C g) × (t ⊧C f → t ⊧C j) → t ⊧C f → t ⊧C g × t ⊧C j
      proof⇐C (⊧f⇒g , ⊧f⇒j) = < ⊧f⇒g , ⊧f⇒j >

      proof⇐HT : i ⊧HT ((f ⇒ g) ∧ (f ⇒ j)) → i ⊧HT (f ⇒ (g ∧ j))
      proof⇐HT ((⊧HTf⇒g , ⊧Cf⇒g) , (⊧HTf⇒j , ⊧Cf⇒j)) =
        < ⊧HTf⇒g , ⊧HTf⇒j > ,
        proof⇐C (⊧Cf⇒g , ⊧Cf⇒j)

-- 1) DNF ⇒ CNF to DNF ⇒ SD ----------------------------------------------------
-- i.e. disjunctive conjunctive rules (DCR) are equivalent to disjunctive simple
-- disjunctive logic programs (DSDLP)
-- first, we prove three helper lemmas 1.1, 1.2, and 1.3
-- 1.1) DNF ⇒ SD is a DSDLP (by definition)
dnf⇒sd-eq-dsdlp : ((ϕ , _) : DNF) → ((ψ , _) : SD) →
                   Σ[ (Π , _) ∈ DSDLP ] ((ϕ ⇒ ψ) ≡HT Th2F Π)
dnf⇒sd-eq-dsdlp (ϕ , ϕp) (ψ , ψp) =
  let
    Π = (ϕ ⇒ ψ) ∷ []
    Πp = (ϕp , ψp) , tt
    ϕ⇒ψ≡Π = ϕ ⇒ ψ                       ≡HT⟨ symm⇔ ⊤-rid-∧ ⟩
              (ϕ ⇒ ψ) ∧ ⊤                 ≡HT⟨def⟩
              (ϕ ⇒ ψ) ∧ Th2F [] ≡HT⟨def⟩
              Th2F Π            ■
  in
    (Π , Πp) , ϕ⇒ψ≡Π

-- 1.2) appending DSDLPs is a DSDLP
DSDLP++DSDLPisDSDLP : ((Γ1 , _) : DSDLP) → ((Γ2 , _) : DSDLP) →
                      isDSDLP (Γ1 ++ Γ2)
DSDLP++DSDLPisDSDLP ([] , tt) (Γ2 , Γ2p) = Γ2p
DSDLP++DSDLPisDSDLP ((r ∷ Γ1) , (rp , Γ1p)) (Γ2 , Γ2p) =
  rp , DSDLP++DSDLPisDSDLP (Γ1 , Γ1p) (Γ2 , Γ2p)

-- 1.3) the conjunction of two DSDLPs is a DSDLP
dsdlp∧dsdlp-eq-dsdlp : ((Γ1 , _) (Γ2 , _) : DSDLP) →
                       Σ[ (Π , _) ∈ DSDLP ] ((Th2F Γ1 ∧ Th2F Γ2) ≡HT (Th2F Π))
dsdlp∧dsdlp-eq-dsdlp Γ1 Γ2 =
  ((p1 Γ1) ++ (p1 Γ2) , DSDLP++DSDLPisDSDLP Γ1 Γ2) ,
  Th∧Th-eq-Th++Th

-- finally, for every DCR there is an equivalent DSDLP
dcr-eq-dsdlp : ((ϕ , _) : DCR) → Σ[ (Π , _) ∈ DSDLP ] (ϕ ≡HT Th2F Π)
-- base cases: conversion with dnf⇒sd-eq-dsdlp
dcr-eq-dsdlp (ϕ ⇒ ⊥ , (ϕp , tt)) =
  dnf⇒sd-eq-dsdlp (ϕ , ϕp) (⊥ , tt)
dcr-eq-dsdlp (ϕ ⇒ V x , (ϕp , tt)) =
  dnf⇒sd-eq-dsdlp (ϕ , ϕp) (V x , tt)
dcr-eq-dsdlp (ϕ ⇒ (ψ1 ∨ ψ2) , (ϕp , ψp)) =
  dnf⇒sd-eq-dsdlp (ϕ , ϕp) (ψ1 ∨ ψ2 , ψp)
dcr-eq-dsdlp (ϕ ⇒ (ψ1 ⇒ ψ2) , (ϕp , ψp)) =
  dnf⇒sd-eq-dsdlp (ϕ , ϕp) (ψ1 ⇒ ψ2 , ψp)
-- step case
dcr-eq-dsdlp (ϕ ⇒ (ψ1 ∧ ψ2) , (ϕp , (ψ1p , ψ2p))) =
  let
    -- we make use of the equivalence ϕ ⇒ (ψ1 ∧ ψ2) ≡ (ϕ ⇒ ψ1) ∧ (ϕ ⇒ ψ2)
    -- first, we convert ϕ ⇒ ψ1 to Γ1
    ((Γ1 , Γ1p) , ϕ⇒ψ1≡Γ1) = dcr-eq-dsdlp (ϕ ⇒ ψ1 , (ϕp , ψ1p))
    -- next, we convert ϕ ⇒ ψ2 to Γ2
    ((Γ2 , Γ2p) , ϕ⇒ψ2≡Γ2) = dcr-eq-dsdlp (ϕ ⇒ ψ2 , (ϕp , ψ2p))
    -- combining Γ1 and Γ2 to Π
    ((Π , Πp) , Γ1∧Γ2≡Π) = dsdlp∧dsdlp-eq-dsdlp (Γ1 , Γ1p) (Γ2 , Γ2p)
    -- ϕ ⇒ (ψ1 ∧ ψ2) is equivalent to Π
    eq = ϕ ⇒ (ψ1 ∧ ψ2)
           ≡HT⟨ rem∧head ⟩
         (ϕ ⇒ ψ1) ∧ (ϕ ⇒ ψ2)
           ≡HT⟨ replace∧lhs ϕ⇒ψ1≡Γ1 ⟩
         Th2F Γ1 ∧ (ϕ ⇒ ψ2)
           ≡HT⟨ replace∧rhs ϕ⇒ψ2≡Γ2 ⟩
         Th2F Γ1 ∧ Th2F Γ2
           ≡HT⟨ Γ1∧Γ2≡Π ⟩
         Th2F (Γ1 ++ Γ2)
           ≡HT⟨def⟩
         Th2F Π ■
  in
    (Π , Πp) , eq

-- 2) DNF ⇒ SD to SC ⇒ SD ------------------------------------------------------
-- i.e. disjunctive simple disjunctive rules (DCDR) are equivalent to
-- simple conjunctive disjunctive logic programs (SCDLP)
-- first, we prove three helper lemmas 2.1, 2.2, and 2.3
-- 2.1) SC ⇒ SD is a SCDLP (by definition)
sc⇒sd-eq-scdlp : ((ϕ , ϕp) : SC) → ((ψ , ψp) : SD) →
                 Σ[ (Π , _) ∈ SCDLP ] ((ϕ ⇒ ψ) ≡HT Th2F Π)
sc⇒sd-eq-scdlp (ϕ , ϕp) (ψ , ψp) =
  let
    Π = (ϕ ⇒ ψ) ∷ []
    Πp = (ϕp , ψp) , tt
    ϕ⇒ψ≡Π = ϕ ⇒ ψ                       ≡HT⟨ symm⇔ ⊤-rid-∧ ⟩
              (ϕ ⇒ ψ) ∧ ⊤                 ≡HT⟨def⟩
              (ϕ ⇒ ψ) ∧ Th2F [] ≡HT⟨def⟩
              Th2F Π            ■
  in
    (Π , Πp) , ϕ⇒ψ≡Π

-- 2.2) appending SCDLPs is a SCDLP
SCDLP++SCDLPisSCDLP : ((Γ1 , _) (Γ2 , _) : SCDLP) → isSCDLP (Γ1 ++ Γ2)
SCDLP++SCDLPisSCDLP ([] , tt) (Γ2 , Γ2p) = Γ2p
SCDLP++SCDLPisSCDLP (ϕ ∷ Γ1 , (ϕp , Γ1p)) (Γ2 , Γ2p) =
  ϕp , SCDLP++SCDLPisSCDLP (Γ1 , Γ1p) (Γ2 , Γ2p)

-- 2.3) the conjunction of two SCDLPs is a SCDLP
scdlp∧scdlp-eq-scdlp : ((Γ1 , _) (Γ2 , _) : SCDLP) →
                       Σ[ (Π , _) ∈ SCDLP ] ((Th2F Γ1 ∧ Th2F Γ2) ≡HT Th2F Π)
scdlp∧scdlp-eq-scdlp Γ1 Γ2 =
  ((p1 Γ1) ++ (p1 Γ2) , SCDLP++SCDLPisSCDLP Γ1 Γ2) ,
  Th∧Th-eq-Th++Th

dsd-eq-scdlp : ((ϕ , _) : DSD) → Σ[ (Π , _) ∈ SCDLP ] (ϕ ≡HT Th2F Π)
-- base cases: conversion with sc⇒sd-eq-scdlp
dsd-eq-scdlp (⊥ ⇒ ψ , (tt , ψp)) =
  sc⇒sd-eq-scdlp (⊥ , tt) (ψ , ψp)
dsd-eq-scdlp (V x ⇒ ψ , (tt , ψp)) =
  sc⇒sd-eq-scdlp (V x , tt) (ψ , ψp)
dsd-eq-scdlp ((ϕ1 ∧ ϕ2) ⇒ ψ , (ϕp , ψp)) =
  sc⇒sd-eq-scdlp (ϕ1 ∧ ϕ2 , ϕp) (ψ , ψp)
dsd-eq-scdlp ((ϕ1 ⇒ ϕ2) ⇒ ψ , (ϕp , ψp)) =
  sc⇒sd-eq-scdlp (ϕ1 ⇒ ϕ2 , ϕp) (ψ , ψp)
-- step case
dsd-eq-scdlp ((ϕ1 ∨ ϕ2) ⇒ ψ , ((ϕ1p , ϕ2p) , ψp)) =
  let
    -- we make use of the equivalence (ϕ1 ∨ ϕ2) ⇒ ψ ≡ (ϕ1 ⇒ ψ) ∧ (ϕ2 ⇒ ψ)
    -- first, we convert ϕ1 ⇒ ψ to Γ1
    ((Γ1 , Γ1p) , ϕ1⇒ψ≡Γ1) = dsd-eq-scdlp (ϕ1 ⇒ ψ , (ϕ1p , ψp))
    -- next, we convert ϕ2 ⇒ ψ to Γ2
    ((Γ2 , Γ2p) , ϕ2⇒ψ≡Γ2) = dsd-eq-scdlp (ϕ2 ⇒ ψ , (ϕ2p , ψp))
    -- then, we combine Γ1 and Γ2 to Π
    ((Π , Πp) , Γ1∧Γ2≡Π) = scdlp∧scdlp-eq-scdlp (Γ1 , Γ1p) (Γ2 , Γ2p)
    -- finally, (ϕ1 ∨ ϕ2) ⇒ ψ is equivalent to Π
    eq = (ϕ1 ∨ ϕ2) ⇒ ψ
           ≡HT⟨ rem∨body ⟩
         (ϕ1 ⇒ ψ) ∧ (ϕ2 ⇒ ψ)
           ≡HT⟨ replace∧lhs ϕ1⇒ψ≡Γ1 ⟩
         Th2F Γ1 ∧ (ϕ2 ⇒ ψ)
           ≡HT⟨ replace∧rhs ϕ2⇒ψ≡Γ2 ⟩
         Th2F Γ1 ∧ Th2F Γ2
           ≡HT⟨ Γ1∧Γ2≡Π ⟩
         Th2F Π ■
  in
    (Π , Πp) , eq

-- finally, for every DSDLP there is an equivalent SCDLP
dsdlp-eq-scdlp : ((Γ , _) : DSDLP) → Σ[ (Π , _) ∈ SCDLP ] (Th2F Γ ≡HT Th2F Π)
-- base case: empty program
dsdlp-eq-scdlp ([] , tt) = ([] , tt) , refl⇔
-- step case
dsdlp-eq-scdlp (ϕ ∷ Γ , (ϕp , Γp)) =
  let
    -- first, we convert ϕ to Π1
    ((Π1 , Π1p) , ϕ≡Π1) = dsd-eq-scdlp (ϕ , ϕp)
    -- second, we convert Γ to Π2
    ((Π2 , Π2p) , Γ≡Π2) = dsdlp-eq-scdlp (Γ , Γp)
    -- then, we combine Π1 and Π2 to Π
    ((Π , Πp) , Π1∧Π2≡Π) = scdlp∧scdlp-eq-scdlp (Π1 , Π1p) (Π2 , Π2p)
    -- finally, ϕ∷Γ is equivalent to Π
    ϕ∷Γ≡Π = Th2F (ϕ ∷ Γ)   ≡HT⟨def⟩
         ϕ ∧ Th2F Γ        ≡HT⟨ replace∧lhs ϕ≡Π1 ⟩
         Th2F Π1 ∧ Th2F Γ  ≡HT⟨ replace∧rhs Γ≡Π2 ⟩
         Th2F Π1 ∧ Th2F Π2 ≡HT⟨ Π1∧Π2≡Π ⟩
         Th2F Π            ■
  in
    (Π , Πp) , ϕ∷Γ≡Π

-- 3) DNF ⇒ CNF equivalent to SC ⇒ SD ------------------------------------------
-- first, for every DCR there is an equivalent SCDLP
dcr-eq-scdlp : ((ϕ , _) : DCR) → Σ[ (Π , _) ∈ SCDLP ] (ϕ ≡HT Th2F Π)
dcr-eq-scdlp (ϕ , ϕp) =
  let
    -- first we convert to a DSDLP Γ
    ((Γ , Γp) , ϕ≡Γ) = dcr-eq-dsdlp (ϕ , ϕp)
    -- next, we convert Γ to a SCDLP Π
    ((Π , Πp) , Γ≡Π) = dsdlp-eq-scdlp (Γ , Γp)
    -- finally, ϕ is equivalent to Π
    ϕ≡Π = ϕ       ≡HT⟨ ϕ≡Γ ⟩
           Th2F Γ ≡HT⟨ Γ≡Π ⟩
           Th2F Π ■
  in
    (Π , Πp) , ϕ≡Π

-- then, for every DCLP there is an equivalent SCDLP
dclp-eq-scdlp : ((Γ , _) : DCLP) → Σ[ (Π , _) ∈ SCDLP ] (Th2F Γ ≡HT Th2F Π)
-- base case: empty program
dclp-eq-scdlp ([] , tt) = ([] , tt) , refl⇔
-- step case
dclp-eq-scdlp (ϕ ∷ Γ , (ϕp , Γp)) =
  let
    -- first, we convert ϕ to Π1
    ((Π1 , Π1p) , ϕ≡Π1) = dcr-eq-scdlp (ϕ , ϕp)
    -- second, we convert Γ to Π2
    ((Π2 , Π2p) , Γ≡Π2) = dclp-eq-scdlp (Γ , Γp)
    -- then, we combine Π1 and Π2 to Π
    ((Π , Πp) , Π1∧Π2≡Π) = scdlp∧scdlp-eq-scdlp (Π1 , Π1p) (Π2 , Π2p)
    -- finally, ϕ∷Γ is equivalent to Π
    ϕ∷Γ≡Π = Th2F (ϕ ∷ Γ)           ≡HT⟨def⟩
             ϕ ∧ (Th2F Γ)          ≡HT⟨ replace∧lhs ϕ≡Π1 ⟩
             (Th2F Π1) ∧ (Th2F Γ)  ≡HT⟨ replace∧rhs Γ≡Π2 ⟩
             (Th2F Π1) ∧ (Th2F Π2) ≡HT⟨ Π1∧Π2≡Π ⟩
             Th2F Π                ■
  in
    (Π , Πp) , ϕ∷Γ≡Π
