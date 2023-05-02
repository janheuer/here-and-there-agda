module HereAndThere.LogicPrograms.DoubleNegation where

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

∣_∣⊤ : F → ℕ
∣ ⊥ ∣⊤ = 0
∣ (⊥ ⇒ ⊥) ∣⊤ = 1
∣ V x ∣⊤ = 0
∣ f ∧ g ∣⊤ = ∣ f ∣⊤ + ∣ g ∣⊤
∣ f ∨ g ∣⊤ = ∣ f ∣⊤ + ∣ g ∣⊤
∣ f ⇒ g ∣⊤ = ∣ f ∣⊤ + ∣ g ∣⊤

∣_∣⊤×≡ : (f : F) → Σ[ n ∈ ℕ ] (n ≡ ∣ f ∣⊤)
∣ f ∣⊤×≡ = ∣ f ∣⊤ , refl

∣_∣SCD⊤ : SCD → ℕ
∣ (b ⇒ h) , _ ∣SCD⊤ = ∣ h ∣⊤

∣_∣⊥ : F → ℕ
∣ ⊥ ∣⊥ = 1
∣ (⊥ ⇒ ⊥) ∣⊥ = 0
∣ V x ∣⊥ = 0
∣ (V x) ⇒ ⊥ ∣⊥ = 0
∣ ((V x) ⇒ ⊥) ⇒ ⊥ ∣⊥ = 0
∣ f ∧ g ∣⊥ = ∣ f ∣⊥ + ∣ g ∣⊥
∣ f ∨ g ∣⊥ = ∣ f ∣⊥ + ∣ g ∣⊥
∣ f ⇒ g ∣⊥ = ∣ f ∣⊥ + ∣ g ∣⊥

∣_∣⊥×≡ : (f : F) → Σ[ n ∈ ℕ ] (n ≡ ∣ f ∣⊥)
∣ f ∣⊥×≡ = ∣ f ∣⊥ , refl

∣_∣SCD⊥ : SCD → ℕ
∣ (b ⇒ h) , _ ∣SCD⊥ = ∣ b ∣⊥

sd⊤-eq-⊤ : (ϕ : F) → isSD ϕ → {n : ℕ} → {suc n ≡ ∣ ϕ ∣⊤} → (ϕ ≡HT ⊤)
sd⊤-eq-⊤ (⊥ ⇒ ⊥) tt {0} {refl} = refl⇔
sd⊤-eq-⊤ (f ∨ g) (fp , gp) {n} {sn≡∣f∨g∣⊤} with ∣ f ∣⊤×≡
... | 0 , 0≡∣f∣⊤ =
  let
    sn≡∣g∣⊤ = x≡y+z∧0≡y⇒x≡z sn≡∣f∨g∣⊤ 0≡∣f∣⊤
    g≡⊤ = sd⊤-eq-⊤ g gp {n} {sn≡∣g∣⊤}
    f∨g≡⊤ = f ∨ g ≡HT⟨ replace∨rhs g≡⊤ ⟩
            f ∨ ⊤ ≡HT⟨ ⊤-rzero-∨ ⟩
            ⊤ ■
  in
    f∨g≡⊤
... | suc m , sm≡∣f∣⊤ =
  let
    f≡⊤ = sd⊤-eq-⊤ f fp {m} {sm≡∣f∣⊤}
    f∨g≡⊤ = f ∨ g ≡HT⟨ replace∨lhs f≡⊤ ⟩
            ⊤ ∨ g ≡HT⟨ ⊤-lzero-∨ ⟩
            ⊤ ■
  in
    f∨g≡⊤
-- absurd cases
sd⊤-eq-⊤ (V x ⇒ ⊥) ϕp {n} {()}
sd⊤-eq-⊤ (V x ⇒ V x₁) ϕp {n} {()}
sd⊤-eq-⊤ (V x ⇒ (ϕ' ∧ ϕ'')) () {n} {p}
sd⊤-eq-⊤ (V x ⇒ (ϕ' ∨ ϕ'')) () {n} {p}
sd⊤-eq-⊤ (V x ⇒ ⊥ ⇒ ⊥) () {n} {p}
sd⊤-eq-⊤ (V x ⇒ ⊥ ⇒ V x₁) () {n} {p}
sd⊤-eq-⊤ (V x ⇒ ⊥ ⇒ (ϕ'' ∧ ϕ''')) () {n} {p}
sd⊤-eq-⊤ (V x ⇒ ⊥ ⇒ (ϕ'' ∨ ϕ''')) () {n} {p}
sd⊤-eq-⊤ (V x ⇒ ⊥ ⇒ ϕ'' ⇒ ϕ''') () {n} {p}
sd⊤-eq-⊤ (V x ⇒ V x₁ ⇒ ϕ'') () {n} {p}
sd⊤-eq-⊤ (V x ⇒ (ϕ' ∧ ϕ''') ⇒ ϕ'') () {n} {p}
sd⊤-eq-⊤ (V x ⇒ (ϕ' ∨ ϕ''') ⇒ ϕ'') () {n} {p}
sd⊤-eq-⊤ (V x ⇒ (ϕ' ⇒ ϕ''') ⇒ ϕ'') () {n} {p}
sd⊤-eq-⊤ ((V x ⇒ ⊥) ⇒ ⊥) ϕp {n} {()}
sd⊤-eq-⊤ ((V x ⇒ ⊥) ⇒ V x₁) () {n} {p}
sd⊤-eq-⊤ ((V x ⇒ ⊥) ⇒ (ϕ' ∧ ϕ'')) () {n} {p}
sd⊤-eq-⊤ ((V x ⇒ ⊥) ⇒ (ϕ' ∨ ϕ'')) () {n} {p}
sd⊤-eq-⊤ ((V x ⇒ ⊥) ⇒ ϕ' ⇒ ϕ'') () {n} {p}

sc⊥-eq-⊥ : (ϕ : F) → isSC ϕ → {n : ℕ} → {suc n ≡ ∣ ϕ ∣⊥} → (ϕ ≡HT ⊥)
sc⊥-eq-⊥ ⊥ tt {0} {refl} = refl⇔
sc⊥-eq-⊥ (f ∧ g) (fp , gp) {n} {sn≡∣f∧g∣⊥} with ∣ f ∣⊥×≡
... | 0 , 0≡∣f∣⊥ =
  let
    sn≡∣g∣⊥ = x≡y+z∧0≡y⇒x≡z sn≡∣f∧g∣⊥ 0≡∣f∣⊥
    g≡⊥ = sc⊥-eq-⊥ g gp {n} {sn≡∣g∣⊥}
    f∧g≡⊥ = f ∧ g ≡HT⟨ replace∧rhs g≡⊥ ⟩
            f ∧ ⊥ ≡HT⟨ ⊥-rzero-∧ ⟩
            ⊥ ■
  in
    f∧g≡⊥
... | suc m , sm≡∣f∣⊥ =
  let
    f≡⊥ = sc⊥-eq-⊥ f fp {m} {sm≡∣f∣⊥}
    f∧g≡⊥ = f ∧ g ≡HT⟨ replace∧lhs f≡⊥ ⟩
            ⊥ ∧ g ≡HT⟨ ⊥-lzero-∧ ⟩
            ⊥ ■
  in
    f∧g≡⊥
-- absurd cases
sc⊥-eq-⊥ (⊥ ⇒ ⊥) tt {0} {()}
sc⊥-eq-⊥ (⊥ ⇒ ⊥) tt {suc n} {()}
sc⊥-eq-⊥ (V x ⇒ ⊥) fp {n} {()}
sc⊥-eq-⊥ ((V x ⇒ ⊥) ⇒ ⊥) fp {n} {()}
sc⊥-eq-⊥ ((V x ⇒ ⊥) ⇒ V x₁) () {n} {p}
sc⊥-eq-⊥ ((V x ⇒ ⊥) ⇒ (f ∧ f₁)) () {n} {p}
sc⊥-eq-⊥ ((V x ⇒ ⊥) ⇒ (f ∨ f₁)) () {n} {p}
sc⊥-eq-⊥ ((V x ⇒ ⊥) ⇒ f ⇒ f₁) () {n} {p}

⇒⊤-eq-⊤ : ((ϕ , ϕp) : SCD) → {n : ℕ} → {suc n ≡ ∣ (ϕ , ϕp) ∣SCD⊤} → (ϕ ≡HT ⊤)
⇒⊤-eq-⊤ (f ⇒ g , (fp , gp)) {n} {p} =
  let
    g≡⊤ = sd⊤-eq-⊤ g gp {n} {p}
    f⇒g≡⊤ = f ⇒ g ≡HT⟨ replace⇒rhs g≡⊤ ⟩
             f ⇒ ⊤ ≡HT⟨ ⊤-rzero-⇒ ⟩
             ⊤ ■
  in
    f⇒g≡⊤

⊥⇒-eq-⊤ : ((ϕ , ϕp) : SCD) → {n : ℕ} → {suc n ≡ ∣ (ϕ , ϕp) ∣SCD⊥} → (ϕ ≡HT ⊤)
⊥⇒-eq-⊤ (f ⇒ g , (fp , gp)) {n} {p} =
  let
    f≡⊥ = sc⊥-eq-⊥ f fp {n} {p}
    f⇒g≡⊥ = f ⇒ g ≡HT⟨ replace⇒lhs f≡⊥ ⟩
             ⊥ ⇒ g ≡HT⟨ ⊥-lzero-⇒ ⟩
             ⊤ ■
  in
    f⇒g≡⊥

sc-without-⊥-isBE2¬ : ((ϕ , _) : SC) → (0 ≡ ∣ ϕ ∣⊥) → isBE2¬ ϕ
sc-without-⊥-isBE2¬ (V x , tt) p = tt
sc-without-⊥-isBE2¬ (V x ⇒ ⊥ , tt) p = tt
sc-without-⊥-isBE2¬ ((V x ⇒ ⊥) ⇒ ⊥ , tt) p = tt
sc-without-⊥-isBE2¬ (⊥ ⇒ ⊥ , tt) p = tt
sc-without-⊥-isBE2¬ (f ∧ g , (fp , gp)) 0≡∣f∧g∣⊥ =
  let
    0≡∣f∣⊥ = sym (m+n≡0⇒m≡0 (∣ f ∣⊥) {∣ g ∣⊥} (sym 0≡∣f∧g∣⊥))
    0≡∣g∣⊥ = sym (m+n≡0⇒n≡0 (∣ f ∣⊥) {∣ g ∣⊥} (sym 0≡∣f∧g∣⊥))
  in
    sc-without-⊥-isBE2¬ (f , fp) 0≡∣f∣⊥ , sc-without-⊥-isBE2¬ (g , gp) 0≡∣g∣⊥
sc-without-⊥-isBE2¬ (V x ⇒ V x₁ , ()) p
sc-without-⊥-isBE2¬ (V x ⇒ (f ∧ f₁) , ()) p
sc-without-⊥-isBE2¬ (V x ⇒ (f ∨ f₁) , ()) p
sc-without-⊥-isBE2¬ (V x ⇒ f ⇒ f₁ , ()) p
sc-without-⊥-isBE2¬ ((V x ⇒ V x₁) ⇒ f₁ , ()) p
sc-without-⊥-isBE2¬ ((V x ⇒ (f ∧ f₂)) ⇒ f₁ , ()) p
sc-without-⊥-isBE2¬ ((V x ⇒ (f ∨ f₂)) ⇒ f₁ , ()) p
sc-without-⊥-isBE2¬ ((V x ⇒ f ⇒ f₂) ⇒ f₁ , ()) p

sd-without-⊤-isHE2¬ : ((ϕ , _) : SD) → (0 ≡ ∣ ϕ ∣⊤) → isHE2¬ ϕ
sd-without-⊤-isHE2¬ (⊥ , fp) p = tt
sd-without-⊤-isHE2¬ (V x , fp) p = tt
sd-without-⊤-isHE2¬ (V x ⇒ ⊥ , tt) refl = tt
sd-without-⊤-isHE2¬ ((V x ⇒ ⊥) ⇒ ⊥ , tt) refl = tt
sd-without-⊤-isHE2¬ (f ∨ g , (fp , gp)) 0≡∣f∨g∣⊤ =
  let
    0≡∣f∣⊤ = sym (m+n≡0⇒m≡0 (∣ f ∣⊤) {∣ g ∣⊤} (sym 0≡∣f∨g∣⊤))
    0≡∣g∣⊤ = sym (m+n≡0⇒n≡0 (∣ f ∣⊤) {∣ g ∣⊤} (sym 0≡∣f∨g∣⊤))
  in
    sd-without-⊤-isHE2¬ (f , fp) 0≡∣f∣⊤ , sd-without-⊤-isHE2¬ (g , gp) 0≡∣g∣⊤
sd-without-⊤-isHE2¬ (⊥ ⇒ ⊥ , tt) ()
sd-without-⊤-isHE2¬ (⊥ ⇒ V x , ()) p
sd-without-⊤-isHE2¬ (⊥ ⇒ (f ∧ f₁) , ()) p
sd-without-⊤-isHE2¬ (⊥ ⇒ (f ∨ f₁) , ()) p
sd-without-⊤-isHE2¬ (⊥ ⇒ f ⇒ f₁ , ()) p

scd-eq-lp2¬ : ((ϕ , ϕp) : SCD)
              → {n : ℕ} → {n ≡ ∣ (ϕ , ϕp) ∣SCD⊥}
              → {m : ℕ} → {m ≡ ∣ (ϕ , ϕp) ∣SCD⊤}
              → Σ[ (Π , _) ∈ LP2¬ ] (ϕ ≡HT Th2F Π)
scd-eq-lp2¬ (f ⇒ g , (fp , gp)) {0} {0≡∣f∣⊥} {0} {0≡∣g∣⊤} =
  let
    fisBE2¬ = sc-without-⊥-isBE2¬ (f , fp) 0≡∣f∣⊥
    gisHE2¬ = sd-without-⊤-isHE2¬ (g , gp) 0≡∣g∣⊤
    ϕ = f ⇒ g
    ϕp = fisBE2¬ , gisHE2¬
    Π = ϕ ∷ []
    Πp = ϕp , tt
    f⇒g≡Π = symm⇔ ⊤-rid-∧
  in
    (Π , Πp) , f⇒g≡Π
scd-eq-lp2¬ (f ⇒ g , (fp , gp)) {0} {0≡∣f∣⊥} {suc m} {sm≡∣g∣⊤} =
  let
    f⇒g≡⊤ = ⇒⊤-eq-⊤ (f ⇒ g , (fp , gp)) {m} {sm≡∣g∣⊤}
  in
    ([] , tt) , f⇒g≡⊤
scd-eq-lp2¬ (f ⇒ g , fp , gp) {suc n} {sn≡∣f∣⊥} {_} {_} =
  let
    f⇒g≡⊤ = ⊥⇒-eq-⊤ (f ⇒ g , (fp , gp)) {n} {sn≡∣f∣⊥}
  in
    ([] , tt) , f⇒g≡⊤

LP2¬++LP2¬isLP2¬ : ((Γ1 , _) (Γ2 , _) : LP2¬) → isLP2¬ (Γ1 ++ Γ2)
LP2¬++LP2¬isLP2¬ ([] , tt) (Γ , Γp) = Γp
LP2¬++LP2¬isLP2¬ (ϕ ∷ Γ1 , (ϕp , Γ1p)) (Γ2 , Γ2p) = ϕp , LP2¬++LP2¬isLP2¬ (Γ1 , Γ1p) (Γ2 , Γ2p)

scdlp-eq-lp2¬ : ((Γ , _) : SCDLP) → Σ[ (Π , _) ∈ LP2¬ ] (Th2F Γ ≡HT Th2F Π)
scdlp-eq-lp2¬ ([] , tt) = ([] , tt) , refl⇔
scdlp-eq-lp2¬ (ϕ ∷ Γ , (ϕp , Γp)) =
  let
    ((Π1 , Π1p) , ϕ≡Π1) = scd-eq-lp2¬ (ϕ , ϕp) {∣ ϕ , ϕp ∣SCD⊥} {refl} {∣ ϕ , ϕp ∣SCD⊤} {refl}
    ((Π2 , Π2p) , Γ≡Π2) = scdlp-eq-lp2¬ (Γ , Γp)
    Π = Π1 ++ Π2
    Πp = LP2¬++LP2¬isLP2¬ (Π1 , Π1p) (Π2 , Π2p)
    ϕ∷Γ≡Π = Th2F (ϕ ∷ Γ)       ≡HT⟨def⟩
             ϕ ∧ Th2F Γ         ≡HT⟨ replace∧lhs ϕ≡Π1 ⟩
             Th2F Π1 ∧ Th2F Γ  ≡HT⟨ replace∧rhs Γ≡Π2 ⟩
             Th2F Π1 ∧ Th2F Π2 ≡HT⟨ Th∧Th-eq-Th++Th ⟩
             Th2F Π ■
  in
    (Π , Πp) , ϕ∷Γ≡Π
