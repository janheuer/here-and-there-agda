module HereAndThere.LogicPrograms.WIP where

open import Agda.Builtin.Unit renaming (⊤ to Unit) using (tt)
open import Data.Empty renaming (⊥ to Ø) using ()
open import Data.Product using (_×_ ; _,_ ; Σ-syntax)
                         renaming (proj₁ to p1)
open import Data.List using (List ; [] ; _∷_)

open import HereAndThere.Base
open import HereAndThere.Equivalences
open import HereAndThere.LogicPrograms.Nested
open import Formula.LogicPrograms
open import Formula.LogicPrograms.Nested
open import Formula.LogicPrograms.DoubleNegation

-- intermediate form to go from nested rules to rules with double negation
isSC : F → Set
isSC ⊥ = Unit
isSC (⊥ ⇒ ⊥) = Unit
isSC (V a) = Unit
isSC ((V a) ⇒ ⊥) = Unit
isSC (((V a) ⇒ ⊥) ⇒ ⊥) = Unit
isSC (f ∧ g) = (isSC f) × (isSC g)
isSC (f ∨ g) = Ø
isSC (f ⇒ g) = Ø

SC : Set
SC = Σ[ f ∈ F ] (isSC f)

isSD : F → Set
isSD ⊥ = Unit
isSD (⊥ ⇒ ⊥) = Unit
isSD (V a) = Unit
isSD ((V a) ⇒ ⊥) = Unit
isSD (((V a) ⇒ ⊥) ⇒ ⊥) = Unit
isSD (f ∧ g) = Ø
isSD (f ∨ g) = (isSC f) × (isSC g)
isSD (f ⇒ g) = Ø

SD : Set
SD = Σ[ f ∈ F ] (isSD f)

isDNF : F → Set
isDNF (f ∨ g) = (isDNF f) × (isDNF g)
isDNF f = isSC f

DNF : Set
DNF = Σ[ f ∈ F ] (isDNF f)

isCNF : F → Set
isCNF (f ∧ g) = (isCNF f) × (isCNF g)
isCNF f = isSD f

CNF : Set
CNF = Σ[ f ∈ F ] (isCNF f)

dnf∧dnf-eq-dnf : ((ϕ , _) : DNF) → ((ψ , _) : DNF) → Σ[ (f , _) ∈ DNF ] ((ϕ ∧ ψ) ≡HT f)
dnf∧dnf-eq-dnf ((ϕ1 ∨ ϕ2) , (ϕ1p , ϕ2p)) (ψ , ψp) =
  let
    ((f , fp) , ϕ1∧ψ≡HTf) = dnf∧dnf-eq-dnf (ϕ1 , ϕ1p) (ψ , ψp)
    ((g , gp) , ϕ2∧ψ≡HTg) = dnf∧dnf-eq-dnf (ϕ2 , ϕ2p) (ψ , ψp)
    ϕ∧ψ≡HTf∨g = (ϕ1 ∨ ϕ2) ∧ ψ       ≡HT⟨ comm∧ ⟩
                ψ ∧ (ϕ1 ∨ ϕ2)       ≡HT⟨ distr∧∨ ⟩
                (ψ ∧ ϕ1) ∨ (ψ ∧ ϕ2) ≡HT⟨ replace∨lhs comm∧ ⟩
                (ϕ1 ∧ ψ) ∨ (ψ ∧ ϕ2) ≡HT⟨ replace∨rhs comm∧ ⟩
                (ϕ1 ∧ ψ) ∨ (ϕ2 ∧ ψ) ≡HT⟨ replace∨lhs ϕ1∧ψ≡HTf ⟩
                f ∨ (ϕ2 ∧ ψ)        ≡HT⟨ replace∨rhs ϕ2∧ψ≡HTg ⟩
                f ∨ g               ■
  in
    (f ∨ g , (fp , gp)) , ϕ∧ψ≡HTf∨g
dnf∧dnf-eq-dnf (ϕ , ϕp) (ψ , ψp) = {!!}

¬⊤-eq-⊥ : ((⊥ ⇒ ⊥) ⇒ ⊥) ≡HT ⊥
¬⊤-eq-⊥ i@(IHT h t p) =
  let
    proof⇒C ⊧⊤⇒⊥ = ⊧⊤⇒⊥ (λ x → x)
    proof⇒HT = λ (_ , y) → y (λ x → x)
    proof⇐C ⊧⊥ = λ _ → ⊧⊥
    proof⇐HT ⊧⊥ = (λ _ → ⊧⊥) , (λ _ → ⊧⊥)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

ne-eq-dnf : ((ϕ , _) : NE) → Σ[ (f , _) ∈ DNF ] (ϕ ≡HT f)
ne-eq-dnf (⊥ , p) = (⊥ , tt) , refl⇔
ne-eq-dnf (V a , p) = ((V a) , tt) , refl⇔
ne-eq-dnf (f ∧ g , (fp , gp)) =
  let
    ((ψ1 , ψ1p) , f≡HTψ1) = ne-eq-dnf (f , fp)
    ((ψ2 , ψ2p) , g≡HTψ2) = ne-eq-dnf (g , gp)
    ((ϕ , ϕp) , ψ1∧ψ2≡HTϕ) = dnf∧dnf-eq-dnf (ψ1 , ψ1p) (ψ2 , ψ2p)
    f∧g≡HTϕ = f  ∧ g  ≡HT⟨ replace∧lhs f≡HTψ1 ⟩
              ψ1 ∧ g  ≡HT⟨ replace∧rhs g≡HTψ2 ⟩
              ψ1 ∧ ψ2 ≡HT⟨ ψ1∧ψ2≡HTϕ ⟩
              ϕ       ■
  in
   (ϕ , ϕp) , f∧g≡HTϕ
ne-eq-dnf (f ∨ g , (fp , gp)) =
  let
    ((ψ1 , ψ1p) , f≡HTψ1) = ne-eq-dnf (f , fp)
    ((ψ2 , ψ2p) , g≡HTψ2) = ne-eq-dnf (g , gp)
    ϕ = ψ1 ∨ ψ2
    ϕp = ψ1p , ψ2p
    f∨g≡HTϕ = f  ∨ g  ≡HT⟨ replace∨lhs f≡HTψ1 ⟩
              ψ1 ∨ g  ≡HT⟨ replace∨rhs g≡HTψ2 ⟩
              ψ1 ∨ ψ2 ≡HT⟨def⟩
              ϕ       ■
  in
    (ϕ , ϕp) , f∨g≡HTϕ
-- trivial
ne-eq-dnf (⊥ ⇒ ⊥ , p) = ((⊥ ⇒ ⊥) , tt) , refl⇔
ne-eq-dnf (V x ⇒ ⊥ , p) = (V x ⇒ ⊥ , tt) , refl⇔
-- de-morgan
ne-eq-dnf ((f ∧ g) ⇒ ⊥ , p) = {!!}
ne-eq-dnf ((f ∨ g) ⇒ ⊥ , p) = {!!}
-- trivial
ne-eq-dnf ((⊥ ⇒ ⊥) ⇒ ⊥ , p) = (⊥ , tt) , ¬⊤-eq-⊥
ne-eq-dnf ((V x ⇒ ⊥) ⇒ ⊥ , p) = (((V x ⇒ ⊥) ⇒ ⊥) , tt) , refl⇔
-- negated de-morgan
ne-eq-dnf (((f ∧ g) ⇒ ⊥) ⇒ ⊥ , p) = {!!}
ne-eq-dnf (((f ∨ g) ⇒ ⊥) ⇒ ⊥ , p) = {!!}
-- removal of two negations
ne-eq-dnf (((f ⇒ ⊥) ⇒ ⊥) ⇒ ⊥ , p) = {!!}

