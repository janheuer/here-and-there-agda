module HereAndThere.LogicPrograms.DisjunctiveConjunctive where

-- for every nested logic program there exists an equivalent disjunctive
-- conjunctive logic program (i.e., rules of the form DNF ⇒ CNF )
-- this uses the fact that nested expressions can be equivalently
-- rewritten as a DNF or CNF (both are possible)

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

-- A) conjunction of DNFs is a DNF ---------------------------------------------
-- we start with two helper lemmas A1 and A2

-- A1) conjunction of simple conjunctions is a disjunctive normal form
-- (really sc ∧ sc is a simple conjunction itself, thus also a dnf)
sc∧sc-eq-dnf : ((ϕ , _) : SC) → ((ψ , _) : SC) →
               Σ[ (f , _) ∈ DNF ] ((ϕ ∧ ψ) ≡HT f)
sc∧sc-eq-dnf (ϕ , ϕp) (ψ , ψp) = ((ϕ ∧ ψ) , (ϕp , ψp)) , refl⇔

-- A2) the conjunction of a simple conjunction and a DNF is a DNF itself
sc∧dnf-eq-dnf : (ϕ : F) → isSC ϕ → ((ψ , _) : DNF) → Σ[ (f , _) ∈ DNF ] ((ϕ ∧ ψ) ≡HT f)
-- base cases: the dnf is a simple conjunction
sc∧dnf-eq-dnf ϕ ϕp (⊥ , tt) = sc∧sc-eq-dnf (ϕ , ϕp) (⊥ , tt)
sc∧dnf-eq-dnf ϕ ϕp (V x , tt) = sc∧sc-eq-dnf (ϕ , ϕp) (V x , tt)
sc∧dnf-eq-dnf ϕ ϕp (ψ ∧ ψ' , ψp) = sc∧sc-eq-dnf (ϕ , ϕp) ((ψ ∧ ψ') , ψp)
sc∧dnf-eq-dnf ϕ ϕp (ψ ⇒ ψ' , ψp) = sc∧sc-eq-dnf (ϕ , ϕp) ((ψ ⇒ ψ') , ψp)
-- step case
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

-- finally, the conjunction of dnfs is a dnf itself
dnf∧dnf-eq-dnf : ((ϕ , _) : DNF) → ((ψ , _) : DNF) → Σ[ (f , _) ∈ DNF ] ((ϕ ∧ ψ) ≡HT f)
-- base cases: the first dnf is a simple conjunction
dnf∧dnf-eq-dnf (⊥ , tt) (ψ , ψp) = sc∧dnf-eq-dnf ⊥ tt (ψ , ψp)
dnf∧dnf-eq-dnf (V x , tt) (ψ , ψp) = sc∧dnf-eq-dnf (V x) tt (ψ , ψp)
dnf∧dnf-eq-dnf (ϕ ∧ ϕ' , ϕp) (ψ , ψp) = sc∧dnf-eq-dnf (ϕ ∧ ϕ') ϕp (ψ , ψp)
dnf∧dnf-eq-dnf (ϕ ⇒ ϕ' , ϕp) (ψ , ψp) = sc∧dnf-eq-dnf (ϕ ⇒ ϕ') ϕp (ψ , ψp)
-- step case
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

-- B) disjunction of CNFs is a CNF ---------------------------------------------
-- we start with two helper lemmas B1 and B2

-- B1) disjunction of simple disjunctions is a conjunctive normal form
-- (really sd ∨ sd is a simple disjunction itself, thus also a cnf)
sd∨sd-eq-cnf : ((ϕ , _) : SD) → ((ψ , _) : SD) →
               Σ[ (f , _) ∈ CNF ] ((ϕ ∨ ψ) ≡HT f)
sd∨sd-eq-cnf (ϕ , ϕp) (ψ , ψp) = ((ϕ ∨ ψ) , (ϕp , ψp)) , refl⇔

-- B2) the disjunction os a simple disjunction and a CNF is a CNF itself
sd∨cnf-eq-cnf : (ϕ : F) → isSD ϕ → ((ψ , _) : CNF) → Σ[ (f , _) ∈ CNF ] ((ϕ ∨ ψ) ≡HT f)
-- base cases: the cnf is a simple disjunction
sd∨cnf-eq-cnf ϕ ϕp (⊥ , tt) = sd∨sd-eq-cnf (ϕ , ϕp) (⊥ , tt)
sd∨cnf-eq-cnf ϕ ϕp (V x , tt) = sd∨sd-eq-cnf (ϕ , ϕp) (V x , tt)
sd∨cnf-eq-cnf ϕ ϕp (ψ ∨ ψ' , ψp) = sd∨sd-eq-cnf (ϕ , ϕp) (ψ ∨ ψ' , ψp)
sd∨cnf-eq-cnf ϕ ϕp (ψ ⇒ ψ' , ψp) = sd∨sd-eq-cnf (ϕ , ϕp) (ψ ⇒ ψ' , ψp)
-- step case
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

-- finally, the disjunction of two cnfs is a cnf itself
cnf∨cnf-eq-cnf : ((ϕ , _) : CNF) → ((ψ , _) : CNF) → Σ[ (f , _) ∈ CNF ] ((ϕ ∨ ψ) ≡HT f)
-- base cases: the first cnf is a simple disjunction
cnf∨cnf-eq-cnf (⊥ , tt) (ψ , ψp) = sd∨cnf-eq-cnf ⊥ tt (ψ , ψp)
cnf∨cnf-eq-cnf (V x , tt) (ψ , ψp) = sd∨cnf-eq-cnf (V x) tt (ψ , ψp)
cnf∨cnf-eq-cnf (ϕ ∨ ϕ' , ϕp) (ψ , ψp) = sd∨cnf-eq-cnf (ϕ ∨ ϕ') ϕp (ψ , ψp)
cnf∨cnf-eq-cnf (ϕ ⇒ ϕ' , ϕp) (ψ , ψp) = sd∨cnf-eq-cnf (ϕ ⇒ ϕ') ϕp (ψ , ψp)
-- step case
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

-- C) negation of a CNF is equivalent to a DNF ---------------------------------
-- we start with three helper lemmas C1, C2, and C3

-- C1) the negation of a simple disjunction is a simple disjunction
¬sd-eq-sc : ((ϕ , _) : SD) → Σ[ (ψ , _) ∈ SC ] (¬ ϕ ≡HT ψ)
-- base cases: direct conversion
¬sd-eq-sc (⊥ , tt) = ((⊥ ⇒ ⊥) , tt) , refl⇔
¬sd-eq-sc (⊥ ⇒ ⊥ , tt) = (⊥ , tt) , ¬⊤-eq-⊥
¬sd-eq-sc (V a , tt) = (((V a) ⇒ ⊥) , tt) , refl⇔
¬sd-eq-sc ((V a) ⇒ ⊥ , tt) = ((((V a) ⇒ ⊥) ⇒ ⊥) , tt) , refl⇔
¬sd-eq-sc (((V a) ⇒ ⊥) ⇒ ⊥ , tt) = ((V a) ⇒ ⊥ , tt) , reduce3¬
-- step case: using de morgan law
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

-- C2) a simple disjunction is a DNF (by definition)
isSC-to-isDNF : {f : F} → isSC f → isDNF f
isSC-to-isDNF {⊥} fp = fp
isSC-to-isDNF {V x} fp = fp
isSC-to-isDNF {f ∧ f₁} fp = fp
isSC-to-isDNF {f ⇒ f₁} fp = fp

-- C3) the negation of a simple disjunction is a DNF
¬sd-eq-dnf : ((ϕ , _) : SD) → Σ[ (ψ , _) ∈ DNF ] (¬ ϕ ≡HT ψ)
¬sd-eq-dnf (ϕ , ϕp) =
  let
    -- using C1 ...
    ((ψ , ψp) , ¬ϕ≡ψ) = ¬sd-eq-sc (ϕ , ϕp)
  in
    -- ... and C2
    (ψ , isSC-to-isDNF ψp) , ¬ϕ≡ψ

-- finally, the negation of a CNF is equivalent to a DNF
¬cnf-eq-dnf : ((ϕ , _) : CNF) → Σ[ (ψ , _) ∈ DNF ] (¬ ϕ ≡HT ψ)
-- base cases: the dnf is a simple disjunction
¬cnf-eq-dnf (⊥ , tt) = ¬sd-eq-dnf (⊥ , tt)
¬cnf-eq-dnf (V x , tt) = ¬sd-eq-dnf (V x , tt)
¬cnf-eq-dnf (ϕ ∨ ψ , ϕp) = ¬sd-eq-dnf (ϕ ∨ ψ , ϕp)
¬cnf-eq-dnf (ϕ ⇒ ψ , ϕp) = ¬sd-eq-dnf (ϕ ⇒ ψ , ϕp)
-- step case: de morgan law
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

-- D) negation of a DNF is equivalent to a CNF ---------------------------------
-- we start with three helper lemmas D1, D2, and D3

-- D1) the negation of a simple conjunction is a simple disjunction
¬sc-eq-sd : ((ϕ , _) : SC) → Σ[ (ψ , _) ∈ SD ] (¬ ϕ ≡HT ψ)
-- base cases: direct conversion
¬sc-eq-sd (⊥ , tt) = ((⊥ ⇒ ⊥) , tt) , refl⇔
¬sc-eq-sd (⊥ ⇒ ⊥ , tt) = (⊥ , tt) , ¬⊤-eq-⊥
¬sc-eq-sd (V a , tt) = (((V a) ⇒ ⊥) , tt) , refl⇔
¬sc-eq-sd ((V a) ⇒ ⊥ , tt) = ((((V a) ⇒ ⊥) ⇒ ⊥) , tt) , refl⇔
¬sc-eq-sd (((V a) ⇒ ⊥ ) ⇒ ⊥ , tt) = (((V a) ⇒ ⊥) , tt) , reduce3¬
-- step case: de morgan law
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
-- absurd cases
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

-- D2) a simple disjunction is a CNF (by definition)
isSD-to-isCNF : {f : F} → isSD f → isCNF f
isSD-to-isCNF {⊥} fp = fp
isSD-to-isCNF {V x} fp = fp
isSD-to-isCNF {f ∨ f₁} fp = fp
isSD-to-isCNF {f ⇒ f₁} fp = fp

-- D3) the negation of a simple conjunction is a CNF
¬sc-eq-cnf : ((ϕ , _) : SC) → Σ[ (ψ , _) ∈ CNF ] (¬ ϕ ≡HT ψ)
¬sc-eq-cnf (ϕ , ϕp) =
  let
    -- using D1 ...
    ((ψ , ψp) , ¬ϕ≡ψ) = ¬sc-eq-sd (ϕ , ϕp)
  in
    -- ... and D2
    (ψ , isSD-to-isCNF ψp) , ¬ϕ≡ψ


-- finally, the negation of a DNF is equivalent to CNF
¬dnf-eq-cnf : ((ϕ , _) : DNF) → Σ[ (ψ , _) ∈ CNF ] (¬ ϕ ≡HT ψ)
-- base cases: the dnf is a simple conjunction
¬dnf-eq-cnf (⊥ , tt) = ¬sc-eq-cnf (⊥ , tt)
¬dnf-eq-cnf (V x , tt) = ¬sc-eq-cnf (V x , tt)
¬dnf-eq-cnf (ϕ ∧ ψ , ϕp) = ¬sc-eq-cnf (ϕ ∧ ψ , ϕp)
¬dnf-eq-cnf (ϕ ⇒ ψ , ϕp) = ¬sc-eq-cnf (ϕ ⇒ ψ , ϕp)
-- step case: de morgan law
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

-- converting nested expressions to DNFs and CNFs ------------------------------
-- nested expressions are equivalent to DNF/CNF (mutually recursive proof)
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

-- converting nested logic program to disjunctive conjunctive logic programs ---
-- nested rules are equivalent to rules DNF ⇒ CNF, i.e., DCR
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

-- nested logic programs are equivalent to DCLP
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
