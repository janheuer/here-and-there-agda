module HereAndThere.LogicPrograms.DisjunctiveConjunctive where

open import Agda.Builtin.Unit renaming (⊤ to Unit) using (tt)
open import Data.Empty renaming (⊥ to Ø) using ()
open import Data.Product using (_×_ ; _,_ ; Σ-syntax)
                         renaming (proj₁ to p1)
open import Data.List using (List ; [] ; _∷_)
open import Data.Sum using (_⊎_) renaming (inj₁ to inl ; inj₂ to inr)

open import HereAndThere.Base
open import HereAndThere.Equivalences
open import HereAndThere.Tautologies
open import HereAndThere.LogicPrograms.Nested
open import Formula.LogicPrograms
open import Formula.LogicPrograms.Nested
open import Formula.LogicPrograms.DoubleNegation
open import Formula.LogicPrograms.DisjunctiveConjunctive

-- helper lemmas for ne-eq-dnf
-- conjunction of two sc is a dnf
sc∧sc-eq-dnf : ((ϕ , _) : SC) → ((ψ , _) : SC) → Σ[ (f , _) ∈ DNF ] ((ϕ ∧ ψ) ≡HT f)
sc∧sc-eq-dnf (ϕ , ϕp) (ψ , ψp) = ((ϕ ∧ ψ) , (ϕp , ψp)) , refl⇔

sd∨sd-eq-cnf : ((ϕ , _) : SD) → ((ψ , _) : SD) → Σ[ (f , _) ∈ CNF ] ((ϕ ∨ ψ) ≡HT f)
sd∨sd-eq-cnf (ϕ , ϕp) (ψ , ψp) = ((ϕ ∨ ψ) , (ϕp , ψp)) , refl⇔

-- conjunction of sc and dnf is a dnf
sc∧dnf-eq-dnf : (ϕ : F) → isSC ϕ → ((ψ , _) : DNF) → Σ[ (f , _) ∈ DNF ] ((ϕ ∧ ψ) ≡HT f)
sc∧dnf-eq-dnf ϕ ϕp ((ψ1 ∨ ψ2) , (ψ1p , ψ2p)) =
  let
    ((f , fp) , ϕ∧ψ1≡HTf) = sc∧dnf-eq-dnf ϕ ϕp (ψ1 , ψ1p)
    ((g , gp) , ϕ∧ψ2≡HTg) = sc∧dnf-eq-dnf ϕ ϕp (ψ2 , ψ2p)
    ϕ∧ψ≡HTf∨g = ϕ ∧ (ψ1 ∨ ψ2)       ≡HT⟨ distr∧∨ ⟩
                (ϕ ∧ ψ1) ∨ (ϕ ∧ ψ2) ≡HT⟨ replace∨lhs ϕ∧ψ1≡HTf ⟩
                f ∨ (ϕ ∧ ψ2)         ≡HT⟨ replace∨rhs ϕ∧ψ2≡HTg ⟩
                f ∨ g                ■
  in
    (f ∨ g , (fp , gp)) , ϕ∧ψ≡HTf∨g
sc∧dnf-eq-dnf ϕ ϕp (⊥ , tt) = sc∧sc-eq-dnf (ϕ , ϕp) (⊥ , tt)
sc∧dnf-eq-dnf ϕ ϕp (V x , tt) = sc∧sc-eq-dnf (ϕ , ϕp) (V x , tt)
sc∧dnf-eq-dnf ϕ ϕp (ψ ∧ ψ' , ψp) = sc∧sc-eq-dnf (ϕ , ϕp) ((ψ ∧ ψ') , ψp)
sc∧dnf-eq-dnf ϕ ϕp (ψ ⇒ ψ' , ψp) = sc∧sc-eq-dnf (ϕ , ϕp) ((ψ ⇒ ψ') , ψp)

sd∨cnf-eq-cnf : (ϕ : F) → isSD ϕ → ((ψ , _) : CNF) → Σ[ (f , _) ∈ CNF ] ((ϕ ∨ ψ) ≡HT f)
sd∨cnf-eq-cnf ϕ ϕp ((ψ1 ∧ ψ2) , (ψ1p , ψ2p)) =
  let
    ((f , fp) , ϕ∨ψ1≡HTf) = sd∨cnf-eq-cnf ϕ ϕp (ψ1 , ψ1p)
    ((g , gp) , ϕ∨ψ2≡HTg) = sd∨cnf-eq-cnf ϕ ϕp (ψ2 , ψ2p)
    ϕ∨ψ≡HTf∧g = ϕ ∨ (ψ1 ∧ ψ2)       ≡HT⟨ distr∨∧ ⟩
                (ϕ ∨ ψ1) ∧ (ϕ ∨ ψ2) ≡HT⟨ replace∧lhs ϕ∨ψ1≡HTf ⟩
                f ∧ (ϕ ∨ ψ2)         ≡HT⟨ replace∧rhs ϕ∨ψ2≡HTg ⟩
                f ∧ g                ■
  in
    (f ∧ g , (fp , gp)) , ϕ∨ψ≡HTf∧g
sd∨cnf-eq-cnf ϕ ϕp (⊥ , tt) = sd∨sd-eq-cnf (ϕ , ϕp) (⊥ , tt)
sd∨cnf-eq-cnf ϕ ϕp (V x , tt) = sd∨sd-eq-cnf (ϕ , ϕp) (V x , tt)
sd∨cnf-eq-cnf ϕ ϕp (ψ ∨ ψ' , ψp) = sd∨sd-eq-cnf (ϕ , ϕp) (ψ ∨ ψ' , ψp)
sd∨cnf-eq-cnf ϕ ϕp (ψ ⇒ ψ' , ψp) = sd∨sd-eq-cnf (ϕ , ϕp) (ψ ⇒ ψ' , ψp)

-- conjunction of two dnf is a dnf
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
dnf∧dnf-eq-dnf (⊥ , tt) (ψ , ψp) = sc∧dnf-eq-dnf ⊥ tt (ψ , ψp)
dnf∧dnf-eq-dnf (V x , tt) (ψ , ψp) = sc∧dnf-eq-dnf (V x) tt (ψ , ψp)
dnf∧dnf-eq-dnf (ϕ ∧ ϕ' , ϕp) (ψ , ψp) = sc∧dnf-eq-dnf (ϕ ∧ ϕ') ϕp (ψ , ψp)
dnf∧dnf-eq-dnf (ϕ ⇒ ϕ' , ϕp) (ψ , ψp) = sc∧dnf-eq-dnf (ϕ ⇒ ϕ') ϕp (ψ , ψp)

cnf∨cnf-eq-cnf : ((ϕ , _) : CNF) → ((ψ , _) : CNF) → Σ[ (f , _) ∈ CNF ] ((ϕ ∨ ψ) ≡HT f)
cnf∨cnf-eq-cnf ((ϕ1 ∧ ϕ2) , (ϕ1p , ϕ2p)) (ψ , ψp) =
  let
    ((f , fp) , ϕ1∨ψ≡HTf) = cnf∨cnf-eq-cnf (ϕ1 , ϕ1p) (ψ , ψp)
    ((g , gp) , ϕ2∨ψ≡HTg) = cnf∨cnf-eq-cnf (ϕ2 , ϕ2p) (ψ , ψp)
    ϕ∨ψ≡HTf∧g = (ϕ1 ∧ ϕ2) ∨ ψ        ≡HT⟨ comm∨ ⟩
                 ψ ∨ (ϕ1 ∧ ϕ2)        ≡HT⟨ distr∨∧ ⟩
                 (ψ ∨ ϕ1) ∧ (ψ ∨ ϕ2) ≡HT⟨ replace∧lhs comm∨ ⟩
                 (ϕ1 ∨ ψ) ∧ (ψ ∨ ϕ2) ≡HT⟨ replace∧rhs comm∨ ⟩
                 (ϕ1 ∨ ψ) ∧ (ϕ2 ∨ ψ) ≡HT⟨ replace∧lhs ϕ1∨ψ≡HTf ⟩
                 f ∧ (ϕ2 ∨ ψ)         ≡HT⟨ replace∧rhs ϕ2∨ψ≡HTg ⟩
                 f ∧ g                ■
  in
    (f ∧ g , (fp , gp)) , ϕ∨ψ≡HTf∧g
cnf∨cnf-eq-cnf (⊥ , tt) (ψ , ψp) = sd∨cnf-eq-cnf ⊥ tt (ψ , ψp)
cnf∨cnf-eq-cnf (V x , tt) (ψ , ψp) = sd∨cnf-eq-cnf (V x) tt (ψ , ψp)
cnf∨cnf-eq-cnf (ϕ ∨ ϕ' , ϕp) (ψ , ψp) = sd∨cnf-eq-cnf (ϕ ∨ ϕ') ϕp (ψ , ψp)
cnf∨cnf-eq-cnf (ϕ ⇒ ϕ' , ϕp) (ψ , ψp) = sd∨cnf-eq-cnf (ϕ ⇒ ϕ') ϕp (ψ , ψp)

-- negation of top is bottom
¬⊤-eq-⊥ : ((⊥ ⇒ ⊥) ⇒ ⊥) ≡HT ⊥
¬⊤-eq-⊥ i@(IHT h t p) =
  let
    proof⇒C ⊧⊤⇒⊥ = ⊧⊤⇒⊥ (λ x → x)
    proof⇒HT = λ (_ , y) → y (λ x → x)
    proof⇐C ⊧⊥ = λ _ → ⊧⊥
    proof⇐HT ⊧⊥ = (λ _ → ⊧⊥) , (λ _ → ⊧⊥)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

¬sd-eq-sc : ((ϕ , _) : SD) → Σ[ (ψ , _) ∈ SC ] (¬ ϕ ≡HT ψ)
¬sd-eq-sc (⊥ , tt) = ((⊥ ⇒ ⊥) , tt) , refl⇔
¬sd-eq-sc (⊥ ⇒ ⊥ , tt) = (⊥ , tt) , ¬⊤-eq-⊥
¬sd-eq-sc (V a , tt) = (((V a) ⇒ ⊥) , tt) , refl⇔
¬sd-eq-sc ((V a) ⇒ ⊥ , tt) = ((((V a) ⇒ ⊥) ⇒ ⊥) , tt) , refl⇔
¬sd-eq-sc (((V a) ⇒ ⊥) ⇒ ⊥ , tt) = ((V a) ⇒ ⊥ , tt) , reduce3¬
¬sd-eq-sc (f ∨ g , (fp , gp)) =
  let
    ((ψ1 , ψ1p) , ¬f≡ψ1) = ¬sd-eq-sc (f , fp)
    ((ψ2 , ψ2p) , ¬g≡ψ2) = ¬sd-eq-sc (g , gp)
    ϕ = ψ1 ∧ ψ2
    ϕp = ψ1p , ψ2p
    ¬f∨g≡ϕ = ¬ (f ∨ g) ≡HT⟨ demorgan∨ ⟩
             ¬ f ∧ ¬ g ≡HT⟨ replace∧lhs ¬f≡ψ1 ⟩
             ψ1 ∧ ¬ g  ≡HT⟨ replace∧rhs ¬g≡ψ2 ⟩
             ψ1 ∧ ψ2  ≡HT⟨def⟩
             ϕ        ■
  in
    (ϕ , ϕp) , ¬f∨g≡ϕ
--absurd cases
¬sd-eq-sc (f ∧ g , ())
¬sd-eq-sc ((V x ⇒ V x₁) ⇒ ⊥ , ())
¬sd-eq-sc ((V x ⇒ (f ∧ f₁)) ⇒ ⊥ , ())
¬sd-eq-sc ((V x ⇒ (f ∨ f₁)) ⇒ ⊥ , ())
¬sd-eq-sc ((V x ⇒ f ⇒ f₁) ⇒ ⊥ , ())
¬sd-eq-sc ((V x₁ ⇒ ⊥) ⇒ V x , ())
¬sd-eq-sc ((V x₁ ⇒ V x₂) ⇒ V x , ())
¬sd-eq-sc ((V x₁ ⇒ (f ∧ f₁)) ⇒ V x , ())
¬sd-eq-sc ((V x₁ ⇒ (f ∨ f₁)) ⇒ V x , ())
¬sd-eq-sc ((V x₁ ⇒ f ⇒ f₁) ⇒ V x , ())
¬sd-eq-sc ((V x ⇒ ⊥) ⇒ (g ∧ g₁) , ())
¬sd-eq-sc ((V x ⇒ V x₁) ⇒ (g ∧ g₁) , ())
¬sd-eq-sc ((V x ⇒ (f ∧ f₁)) ⇒ (g ∧ g₁) , ())
¬sd-eq-sc ((V x ⇒ (f ∨ f₁)) ⇒ (g ∧ g₁) , ())
¬sd-eq-sc ((V x ⇒ f ⇒ f₁) ⇒ (g ∧ g₁) , ())
¬sd-eq-sc ((V x ⇒ ⊥) ⇒ (g ∨ g₁) , ())
¬sd-eq-sc ((V x ⇒ V x₁) ⇒ (g ∨ g₁) , ())
¬sd-eq-sc ((V x ⇒ (f ∧ f₁)) ⇒ (g ∨ g₁) , ())
¬sd-eq-sc ((V x ⇒ (f ∨ f₁)) ⇒ (g ∨ g₁) , ())
¬sd-eq-sc ((V x ⇒ f ⇒ f₁) ⇒ (g ∨ g₁) , ())
¬sd-eq-sc ((V x ⇒ ⊥) ⇒ g ⇒ g₁ , ())
¬sd-eq-sc ((V x ⇒ V x₁) ⇒ g ⇒ g₁ , ())
¬sd-eq-sc ((V x ⇒ (f ∧ f₁)) ⇒ g ⇒ g₁ , ())
¬sd-eq-sc ((V x ⇒ (f ∨ f₁)) ⇒ g ⇒ g₁ , ())
¬sd-eq-sc ((V x ⇒ f ⇒ f₁) ⇒ g ⇒ g₁ , ())

¬sc-eq-sd : ((ϕ , _) : SC) → Σ[ (ψ , _) ∈ SD ] (¬ ϕ ≡HT ψ)
¬sc-eq-sd (⊥ , tt) = ((⊥ ⇒ ⊥) , tt) , refl⇔
¬sc-eq-sd (⊥ ⇒ ⊥ , tt) = (⊥ , tt) , ¬⊤-eq-⊥
¬sc-eq-sd (V a , tt) = (((V a) ⇒ ⊥) , tt) , refl⇔
¬sc-eq-sd ((V a) ⇒ ⊥ , tt) = ((((V a) ⇒ ⊥) ⇒ ⊥) , tt) , refl⇔
¬sc-eq-sd (((V a) ⇒ ⊥ ) ⇒ ⊥ , tt) = (((V a) ⇒ ⊥) , tt) , reduce3¬
¬sc-eq-sd (f ∧ g , (fp , gp)) =
  let
    ((ψ1 , ψ1p) , ¬f≡ψ1) = ¬sc-eq-sd (f , fp)
    ((ψ2 , ψ2p) , ¬g≡ψ2) = ¬sc-eq-sd (g , gp)
    ϕ = ψ1 ∨ ψ2
    ϕp = ψ1p , ψ2p
    ¬f∧g≡ϕ = ¬ (f ∧ g) ≡HT⟨ demorgan∧ ⟩
             ¬ f ∨ ¬ g ≡HT⟨ replace∨lhs ¬f≡ψ1 ⟩
             ψ1 ∨ ¬ g  ≡HT⟨ replace∨rhs ¬g≡ψ2 ⟩
             ψ1 ∨ ψ2  ≡HT⟨def⟩
             ϕ        ■
  in
    (ϕ , ϕp) , ¬f∧g≡ϕ
¬sc-eq-sd (f ∨ g , ())
¬sc-eq-sd (⊥ ⇒ V x , ())
¬sc-eq-sd (⊥ ⇒ (g ∧ g₁) , ())
¬sc-eq-sd (⊥ ⇒ (g ∨ g₁) , ())
¬sc-eq-sd (⊥ ⇒ g ⇒ g₁ , ())
¬sc-eq-sd (V x ⇒ V x₁ , ())
¬sc-eq-sd (V x ⇒ (g ∧ g₁) , ())
¬sc-eq-sd (V x ⇒ (g ∨ g₁) , ())
¬sc-eq-sd (V x ⇒ g ⇒ g₁ , ())
¬sc-eq-sd ((V x ⇒ ⊥) ⇒ V x₁ , ())
¬sc-eq-sd ((V x ⇒ ⊥) ⇒ (g ∧ g₁) , ())
¬sc-eq-sd ((V x ⇒ ⊥) ⇒ (g ∨ g₁) , ())
¬sc-eq-sd ((V x ⇒ ⊥) ⇒ g ⇒ g₁ , ())

isSC-to-isDNF : {f : F} → isSC f → isDNF f
isSC-to-isDNF {⊥} fp = fp
isSC-to-isDNF {V x} fp = fp
isSC-to-isDNF {f ∧ f₁} fp = fp
isSC-to-isDNF {f ⇒ f₁} fp = fp

¬sd-eq-dnf : ((ϕ , _) : SD) → Σ[ (ψ , _) ∈ DNF ] (¬ ϕ ≡HT ψ)
¬sd-eq-dnf (ϕ , ϕp) =
  let
    ((ψ , ψp) , ¬ϕ≡ψ) = ¬sd-eq-sc (ϕ , ϕp)
  in
    (ψ , isSC-to-isDNF ψp) , ¬ϕ≡ψ

isSD-to-isCNF : {f : F} → isSD f → isCNF f
isSD-to-isCNF {⊥} fp = fp
isSD-to-isCNF {V x} fp = fp
isSD-to-isCNF {f ∨ f₁} fp = fp
isSD-to-isCNF {f ⇒ f₁} fp = fp

¬sc-eq-cnf : ((ϕ , _) : SC) → Σ[ (ψ , _) ∈ CNF ] (¬ ϕ ≡HT ψ)
¬sc-eq-cnf (ϕ , ϕp) =
  let
    ((ψ , ψp) , ¬ϕ≡ψ) = ¬sc-eq-sd (ϕ , ϕp)
  in
    (ψ , isSD-to-isCNF ψp) , ¬ϕ≡ψ

¬cnf-eq-dnf : ((ϕ , _) : CNF) → Σ[ (ψ , _) ∈ DNF ] (¬ ϕ ≡HT ψ)
¬cnf-eq-dnf (ϕ1 ∧ ϕ2 , (ϕ1p , ϕ2p)) =
  let
    ((ψ1 , ψ1p) , ¬ϕ1≡ψ1) = ¬cnf-eq-dnf (ϕ1 , ϕ1p)
    ((ψ2 , ψ2p) , ¬ϕ2≡ψ2) = ¬cnf-eq-dnf (ϕ2 , ϕ2p)
    f = ψ1 ∨ ψ2
    fp = ψ1p , ψ2p
    ¬ϕ≡f = ¬ (ϕ1 ∧ ϕ2) ≡HT⟨ demorgan∧ ⟩
           ¬ ϕ1 ∨ ¬ ϕ2 ≡HT⟨ replace∨lhs ¬ϕ1≡ψ1 ⟩
           ψ1 ∨ ¬ ϕ2   ≡HT⟨ replace∨rhs ¬ϕ2≡ψ2 ⟩
           ψ1 ∨ ψ2     ≡HT⟨def⟩
           f           ■
  in
    (f , fp) , ¬ϕ≡f
¬cnf-eq-dnf (⊥ , tt) = ¬sd-eq-dnf (⊥ , tt)
¬cnf-eq-dnf (V x , tt) = ¬sd-eq-dnf (V x , tt)
¬cnf-eq-dnf (ϕ ∨ ψ , ϕp) = ¬sd-eq-dnf (ϕ ∨ ψ , ϕp)
¬cnf-eq-dnf (ϕ ⇒ ψ , ϕp) = ¬sd-eq-dnf (ϕ ⇒ ψ , ϕp)

¬dnf-eq-cnf : ((ϕ , _) : DNF) → Σ[ (ψ , _) ∈ CNF ] (¬ ϕ ≡HT ψ)
¬dnf-eq-cnf (ϕ1 ∨ ϕ2 , (ϕ1p , ϕ2p)) =
  let
    ((ψ1 , ψ1p) , ¬ϕ1≡ψ1) = ¬dnf-eq-cnf (ϕ1 , ϕ1p)
    ((ψ2 , ψ2p) , ¬ϕ2≡ψ2) = ¬dnf-eq-cnf (ϕ2 , ϕ2p)
    f = ψ1 ∧ ψ2
    fp = ψ1p , ψ2p
    ¬ϕ≡f = ¬ (ϕ1 ∨ ϕ2) ≡HT⟨ demorgan∨ ⟩
           ¬ ϕ1 ∧ ¬ ϕ2 ≡HT⟨ replace∧lhs ¬ϕ1≡ψ1 ⟩
           ψ1 ∧ ¬ ϕ2   ≡HT⟨ replace∧rhs ¬ϕ2≡ψ2 ⟩
           ψ1 ∧ ψ2     ≡HT⟨def⟩
           f           ■
  in
    (f , fp) , ¬ϕ≡f
¬dnf-eq-cnf (⊥ , tt) = ¬sc-eq-cnf (⊥ , tt)
¬dnf-eq-cnf (V x , tt) = ¬sc-eq-cnf (V x , tt)
¬dnf-eq-cnf (ϕ ∧ ψ , ϕp) = ¬sc-eq-cnf (ϕ ∧ ψ , ϕp)
¬dnf-eq-cnf (ϕ ⇒ ψ , ϕp) = ¬sc-eq-cnf (ϕ ⇒ ψ , ϕp)

-- LifschitzEtAl1999 Proposition 5 ---------------------------------------------
-- every nested expression is equivalent to a dnf and a cnf
ne-eq-dnf : ((ϕ , _) : NE) → Σ[ (f , _) ∈ DNF ] (ϕ ≡HT f)

ne-eq-cnf : ((ϕ , _) : NE) → Σ[ (f , _) ∈ CNF ] (ϕ ≡HT f)

ne-eq-dnf (⊥ , tt) = (⊥ , tt) , refl⇔
ne-eq-dnf (V a , tt) = ((V a) , tt) , refl⇔
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
ne-eq-dnf (f ⇒ ⊥ , fp) =
  let
    ((ψ , ψp) , f≡ψ) = ne-eq-cnf (f , fp)
    ((ϕ , ϕp) , ¬ψ≡ϕ) = ¬cnf-eq-dnf (ψ , ψp)
    ¬f≡ϕ = ¬ f ≡HT⟨ replace¬ f≡ψ ⟩
           ¬ ψ ≡HT⟨ ¬ψ≡ϕ ⟩
           ϕ   ■
  in
    (ϕ , ϕp) , ¬f≡ϕ

ne-eq-cnf (⊥ , tt) = (⊥ , tt) , refl⇔
ne-eq-cnf (V x , tt) = (V x , tt) , refl⇔
ne-eq-cnf (f ∧ g , (fp , gp)) =
  let
    ((ψ1 , ψ1p) , f≡ψ1) = ne-eq-cnf (f , fp)
    ((ψ2 , ψ2p) , g≡ψ2) = ne-eq-cnf (g , gp)
    ϕ = ψ1 ∧ ψ2
    ϕp = ψ1p , ψ2p
    f∧g≡ϕ = f ∧ g    ≡HT⟨ replace∧lhs f≡ψ1 ⟩
            ψ1 ∧ g   ≡HT⟨ replace∧rhs g≡ψ2 ⟩
            ψ1 ∧ ψ2 ≡HT⟨def⟩
            ϕ        ■
  in
    (ϕ , ϕp) , f∧g≡ϕ
ne-eq-cnf (f ∨ g , (fp , gp)) =
  let
    ((ψ1 , ψ1p) , f≡ψ1) = ne-eq-cnf (f , fp)
    ((ψ2 , ψ2p) , g≡ψ2) = ne-eq-cnf (g , gp)
    ((ϕ , ϕp) , ψ1∨ψ2≡ϕ) = cnf∨cnf-eq-cnf (ψ1 , ψ1p) (ψ2 , ψ2p)
    f∨g≡ϕ = f ∨ g   ≡HT⟨ replace∨lhs f≡ψ1 ⟩
            ψ1 ∨ g  ≡HT⟨ replace∨rhs g≡ψ2 ⟩
            ψ1 ∨ ψ2 ≡HT⟨ ψ1∨ψ2≡ϕ ⟩
            ϕ       ■
  in
    (ϕ , ϕp) , f∨g≡ϕ
ne-eq-cnf (f ⇒ ⊥ , fp) =
  let
    ((ψ , ψp) , f≡ψ) = ne-eq-dnf (f , fp)
    ((ϕ , ϕp) , ¬ψ≡ϕ) = ¬dnf-eq-cnf (ψ , ψp)
    ¬f≡ϕ = ¬ f ≡HT⟨ replace¬ f≡ψ ⟩
           ¬ ψ ≡HT⟨ ¬ψ≡ϕ ⟩
           ϕ   ■
  in
    (ϕ , ϕp) , ¬f≡ϕ

nr-eq-dcr : ((ϕ , _) : NR) → Σ[ (ψ , _) ∈ DCR ] (ϕ ≡HT ψ)
nr-eq-dcr (ϕ ⇒ ψ , (ϕp , ψp)) =
  let
    ((δ , δp) , ϕ≡δ) = ne-eq-dnf (ϕ , ϕp)
    ((γ , γp) , ψ≡γ) = ne-eq-cnf (ψ , ψp)
    ϕ⇒ψ≡δ⇒γ = ϕ ⇒ ψ ≡HT⟨ replace⇒lhs ϕ≡δ ⟩
                δ ⇒ ψ ≡HT⟨ replace⇒rhs ψ≡γ ⟩
                δ ⇒ γ ■
  in
    ((δ ⇒ γ) , (δp , γp)) , ϕ⇒ψ≡δ⇒γ

nlp-eq-dclp : (Γ : NLP) → Σ[ Π ∈ DCLP ] (NLP2F Γ ≡HT DCLP2F Π)
nlp-eq-dclp ([] , tt) = ([] , tt) , refl⇔
nlp-eq-dclp (ϕ ∷ Γ , (ϕp , Γp)) =
  let
    ((ψ , ψp) , ϕ≡ψ) = nr-eq-dcr (ϕ , ϕp)
    ((Π , Πp) , Γ≡Π) = nlp-eq-dclp (Γ , Γp)
    ϕ∷Γ≡ψ∷Π = NLP2F ((ϕ ∷ Γ) , (ϕp , Γp))   ≡HT⟨def⟩
                ϕ ∧ (NLP2F (Γ , Γp))          ≡HT⟨ replace∧lhs ϕ≡ψ ⟩
                ψ ∧ (NLP2F (Γ , Γp))          ≡HT⟨ replace∧rhs Γ≡Π ⟩
                ψ ∧ (DCLP2F (Π , Πp))        ≡HT⟨def⟩
               DCLP2F ((ψ ∷ Π) , (ψp , Πp)) ■
  in
    (ψ ∷ Π , (ψp , Πp)) , ϕ∷Γ≡ψ∷Π
