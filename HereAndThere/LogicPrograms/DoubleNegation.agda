module HereAndThere.LogicPrograms.DoubleNegation where

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

-- removal of disjunction in body of implications ------------------------------
-- LifschitzEtAl1999 proposition 6 (ii)
-- (f ∨ g) ⇒ j is equivalent to (f ⇒ j) ∧ (g ⇒ j)
rem∨body : (f g j : F) → ((f ∨ g) ⇒ j) ≡HT ((f ⇒ j) ∧ (g ⇒ j))
rem∨body f g j i@(IHT h t p) = (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)
  where
    liftinl : {A B C : Set} → ((A ⊎ B) → C) → A → C
    liftinl f a = f (inl a)

    liftinr : {A B C : Set} → ((A ⊎ B) → C) → B → C
    liftinr f b = f (inr b)

    lift : {A B C : Set} → ((A ⊎ B) → C) → (A → C) × (B → C)
    lift f = liftinl f , liftinr f

    proof⇒C : t ⊧C ((f ∨ g) ⇒ j) → t ⊧C ((f ⇒ j) ∧ (g ⇒ j))
    proof⇒C = lift

    proof⇒HT : i ⊧HT ((f ∨ g) ⇒ j) → i ⊧HT ((f ⇒ j) ∧ (g ⇒ j))
    proof⇒HT (⊧HTf∨g⇒j , ⊧Cf∨g⇒j) =
      (liftinl ⊧HTf∨g⇒j , (p1 (proof⇒C ⊧Cf∨g⇒j))) ,
      (liftinr ⊧HTf∨g⇒j , (p2 (proof⇒C ⊧Cf∨g⇒j)))

    proof⇐C : t ⊧C ((f ⇒ j) ∧ (g ⇒ j)) → t ⊧C ((f ∨ g) ⇒ j)
    proof⇐C (⊧f⇒j , ⊧g⇒j) = [ ⊧f⇒j , ⊧g⇒j ]

    proof⇐HT : i ⊧HT ((f ⇒ j) ∧ (g ⇒ j)) → i ⊧HT ((f ∨ g) ⇒ j)
    proof⇐HT ((⊧HTf⇒j , ⊧Cf⇒j) , (⊧HTg⇒j , ⊧Cg⇒j)) =
      [ ⊧HTf⇒j , ⊧HTg⇒j ] ,
      proof⇐C (⊧Cf⇒j , ⊧Cg⇒j)

-- removal of conjucntion in head of implications ------------------------------
-- LifschitzEtAl1999 proposition 6 (i)
-- f ⇒ (g ∧ j) is equivalent to (f ⇒ g) ∧ (f ⇒ j)
rem∧head : (f g j : F) → (f ⇒ (g ∧ j)) ≡HT ((f ⇒ g) ∧ (f ⇒ j))
rem∧head f g j i@(IHT h t p) = (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)
  where
    liftp1 : {A B C : Set} → (A → (B × C)) → A → B
    liftp1 f a = p1 (f a)

    liftp2 : {A B C : Set} → (A → (B × C)) → A → C
    liftp2 f a = p2 (f a)

    lift : {A B C : Set} → (A → (B × C)) → ((A → B) × (A → C))
    lift f = liftp1 f , liftp2 f

    proof⇒C : t ⊧C (f ⇒ (g ∧ j)) → t ⊧C ((f ⇒ g) ∧ (f ⇒ j))
    proof⇒C = lift

    proof⇒HT : i ⊧HT (f ⇒ (g ∧ j)) → i ⊧HT ((f ⇒ g) ∧ (f ⇒ j))
    proof⇒HT (⊧HTf⇒g∧j , ⊧Cf⇒g∧j) =
      (liftp1 ⊧HTf⇒g∧j , (p1 (proof⇒C ⊧Cf⇒g∧j))) ,
      (liftp2 ⊧HTf⇒g∧j , (p2 (proof⇒C ⊧Cf⇒g∧j)))

    proof⇐C : t ⊧C ((f ⇒ g) ∧ (f ⇒ j)) → t ⊧C (f ⇒ (g ∧ j))
    proof⇐C (⊧f⇒g , ⊧f⇒j) = < ⊧f⇒g , ⊧f⇒j >

    proof⇐HT : i ⊧HT ((f ⇒ g) ∧ (f ⇒ j)) → i ⊧HT (f ⇒ (g ∧ j))
    proof⇐HT ((⊧HTf⇒g , ⊧Cf⇒g) , (⊧HTf⇒j , ⊧Cf⇒j)) =
      < ⊧HTf⇒g , ⊧HTf⇒j > ,
      proof⇐C (⊧Cf⇒g , ⊧Cf⇒j)

-- TODO: lemma SD ∧ .. ∧ SD ← SC ∨ .. ∨ SC is equivalent to { SD ← SC ∨ .. ∨ SC }
dnf⇒sd-eq-dsdlp : ((ϕ , _) : DNF) → ((ψ , _) : SD) → Σ[ Π ∈ DSDLP ] ((ϕ ⇒ ψ) ≡HT DSDLP2F Π)
dnf⇒sd-eq-dsdlp (ϕ , ϕp) (ψ , ψp) =
  let
    Π = (ϕ ⇒ ψ) ∷ []
    Πp = (ϕp , ψp) , tt
    ϕ⇒ψ≡Π = ϕ ⇒ ψ ≡HT⟨ symm⇔ ⊤-rid-∧ ⟩
              (ϕ ⇒ ψ) ∧ ⊤ ≡HT⟨def⟩
              (ϕ ⇒ ψ) ∧ DSDLP2F ([] , tt) ≡HT⟨def⟩
              DSDLP2F ((ϕ ⇒ ψ) ∷ [] , ((ϕp , ψp) , tt)) ■
  in
    (Π , Πp) , ϕ⇒ψ≡Π

DSDLP++DSDLPisDSDLP : ((Γ1 , _) : DSDLP) → ((Γ2 , _) : DSDLP) → isDSDLP (Γ1 ++ Γ2)
DSDLP++DSDLPisDSDLP ([] , tt) (Γ2 , Γ2p) = Γ2p
DSDLP++DSDLPisDSDLP ((r ∷ Γ1) , (rp , Γ1p)) (Γ2 , Γ2p) = rp , DSDLP++DSDLPisDSDLP (Γ1 , Γ1p) (Γ2 , Γ2p)

dsdlp∧dsdlp-eq-dsdlp : (Γ1 Γ2 : DSDLP) → Σ[ Π ∈ DSDLP ] ((DSDLP2F Γ1 ∧ DSDLP2F Γ2) ≡HT (DSDLP2F Π))
dsdlp∧dsdlp-eq-dsdlp Γ1 Γ2 = ((p1 Γ1) ++ (p1 Γ2) , DSDLP++DSDLPisDSDLP Γ1 Γ2) , Th∧Th-eq-Th++Th

dcr-eq-dsdlp : ((ϕ , _) : DCR) → Σ[ Π ∈ DSDLP ] (ϕ ≡HT DSDLP2F Π)
dcr-eq-dsdlp (ϕ ⇒ (ψ1 ∧ ψ2) , (ϕp , (ψ1p , ψ2p))) =
  let
    ϕ⇒ψ1∧ψ2≡ϕ⇒ψ1∧ϕ⇒ψ2 = rem∧head ϕ ψ1 ψ2
    ((Γ1 , Γ1p) , ϕ⇒ψ1≡Γ1) = dcr-eq-dsdlp (ϕ ⇒ ψ1 , (ϕp , ψ1p))
    ((Γ2 , Γ2p) , ϕ⇒ψ2≡Γ2) = dcr-eq-dsdlp (ϕ ⇒ ψ2 , (ϕp , ψ2p))
    ((Π , Πp) , Γ1∧Γ2≡Π) = dsdlp∧dsdlp-eq-dsdlp (Γ1 , Γ1p) (Γ2 , Γ2p)
    eq = ϕ ⇒ (ψ1 ∧ ψ2)                           ≡HT⟨ ϕ⇒ψ1∧ψ2≡ϕ⇒ψ1∧ϕ⇒ψ2 ⟩
         (ϕ ⇒ ψ1) ∧ (ϕ ⇒ ψ2)                    ≡HT⟨ replace∧lhs ϕ⇒ψ1≡Γ1 ⟩
         DSDLP2F (Γ1 , Γ1p) ∧ (ϕ ⇒ ψ2)           ≡HT⟨ replace∧rhs ϕ⇒ψ2≡Γ2 ⟩
         DSDLP2F (Γ1 , Γ1p) ∧ DSDLP2F (Γ2 , Γ2p) ≡HT⟨ Γ1∧Γ2≡Π ⟩
         Th2F (Γ1 ++ Γ2)                          ■
  in
    (Π , Πp) , eq
dcr-eq-dsdlp (ϕ ⇒ ⊥ , (ϕp , tt)) = dnf⇒sd-eq-dsdlp (ϕ , ϕp) (⊥ , tt)
dcr-eq-dsdlp (ϕ ⇒ V x , (ϕp , tt)) = dnf⇒sd-eq-dsdlp (ϕ , ϕp) (V x , tt)
dcr-eq-dsdlp (ϕ ⇒ (ψ1 ∨ ψ2) , (ϕp , ψp)) = dnf⇒sd-eq-dsdlp (ϕ , ϕp) (ψ1 ∨ ψ2 , ψp)
dcr-eq-dsdlp (ϕ ⇒ (ψ1 ⇒ ψ2) , (ϕp , ψp)) = dnf⇒sd-eq-dsdlp (ϕ , ϕp) (ψ1 ⇒ ψ2 , ψp)

-- TODO: lemma SD ← SC ∨ .. ∨ SC is equivalent to { SD ← SC }
dsdlp-eq-scdlp : (Γ : DSDLP) → Σ[ Π ∈ SCDLP ] (DSDLP2F Γ ≡HT SCDLP2F Π)
dsdlp-eq-scdlp = {!!}

dcr-eq-scdlp : ((ϕ , _) : DCR) → Σ[ Π ∈ SCDLP ] (ϕ ≡HT SCDLP2F Π)
dcr-eq-scdlp (ϕ , ϕp) =
  let
    (Γ , ϕ≡Γ) = dcr-eq-dsdlp (ϕ , ϕp)
    (Π , Γ≡Π) = dsdlp-eq-scdlp Γ
    ϕ≡Π = {!!}
    -- ϕ≡Π = trans⇔ ϕ≡Γ Γ≡Π
  in
    Π , ϕ≡Π

SCDLP++SCDLPisSCDLP : ((Γ1 , _) (Γ2 , _) : SCDLP) → isSCDLP (Γ1 ++ Γ2)
SCDLP++SCDLPisSCDLP ([] , tt) (Γ2 , Γ2p) = Γ2p
SCDLP++SCDLPisSCDLP (ϕ ∷ Γ1 , (ϕp , Γ1p)) (Γ2 , Γ2p) = ϕp , SCDLP++SCDLPisSCDLP (Γ1 , Γ1p) (Γ2 , Γ2p)

scdlp∧scdlp-eq-scdlp : (Γ1 Γ2 : SCDLP) → Σ[ Π ∈ SCDLP ] ((SCDLP2F Γ1 ∧ SCDLP2F Γ2) ≡HT SCDLP2F Π)
scdlp∧scdlp-eq-scdlp Γ1 Γ2 = ((p1 Γ1) ++ (p1 Γ2) , SCDLP++SCDLPisSCDLP Γ1 Γ2) , Th∧Th-eq-Th++Th

dclp-eq-scdlp : (Γ : DCLP) → Σ[ Π ∈ SCDLP ] (DCLP2F Γ ≡HT SCDLP2F Π)
dclp-eq-scdlp ([] , tt) = ([] , tt) , refl⇔
dclp-eq-scdlp (ϕ ∷ Γ , (ϕp , Γp)) =
  let
    ((Π1 , Π1p) , ϕ≡Π1) = dcr-eq-scdlp (ϕ , ϕp)
    ((Π2 , Π2p) , Γ≡Π2) = dclp-eq-scdlp (Γ , Γp)
    ((Π , Πp) , Π1∧Π2≡Π) = scdlp∧scdlp-eq-scdlp (Π1 , Π1p) (Π2 , Π2p)
    ϕ∷Γ≡Π = {!!}
  in
    (Π , Πp) , ϕ∷Γ≡Π
