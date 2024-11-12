module HereAndThere.DoubleNegation where

open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Agda.Builtin.Unit using (tt)
open import Data.List using ([] ; _∷_)
open import Data.Product using (_×_ ; _,_ ; Σ-syntax)
                         renaming (proj₁ to p1 ; proj₂ to p2)
open import Data.Nat using (ℕ ; suc ; _+_)
open import Data.Nat.Properties using (m+n≡0⇒m≡0 ; m+n≡0⇒n≡0)
open import Relation.Binary.PropositionalEquality.Core using (sym)

open import HereAndThere
open import Formula.LogicPrograms
open import Formula.LogicPrograms.DoubleNegation
open import NatHelper

-- number of double negated atoms in a formula ---------------------------------
∣_∣2¬ : F → ℕ
∣ ⊥ ∣2¬ = 0
∣ (V a) ∣2¬ = 0
∣ ((V a) ⇒ ⊥) ∣2¬ = 0
∣ (((V a) ⇒ ⊥) ⇒ ⊥) ∣2¬ = 1
∣ f ∧ g ∣2¬ = ∣ f ∣2¬ + ∣ g ∣2¬
∣ f ∨ g ∣2¬ = ∣ f ∣2¬ + ∣ g ∣2¬
∣ f ⇒ g ∣2¬ = ∣ f ∣2¬ + ∣ g ∣2¬

-- helper function to return a number n and a proof that n ≡ ∣f∣2¬
∣_∣2¬×≡ : (f : F) → Σ[ n ∈ ℕ ] (n ≡ ∣ f ∣2¬)
∣ f ∣2¬×≡ = ∣ f ∣2¬ , refl

-- number of double negations in a rule body
∣_∣B2¬ : R2¬ → ℕ
∣ (b ⇒ h) , _ ∣B2¬ = ∣ b ∣2¬

-- convert body expressions with double negation to body expression ------------
-- if a body expression with double negation does not contain double
-- negation, it is a body expression
BE2¬2BE : ((f , _) : BE2¬) → (0 ≡ ∣ f ∣2¬) → isBE f
BE2¬2BE (⊥ ⇒ ⊥ , tt) _ = tt
BE2¬2BE (V x , tt) _ = tt
BE2¬2BE (V x ⇒ ⊥ , tt) _ = tt
BE2¬2BE (f ∧ g , (fp , gp)) 0≡∣f∧g∣2¬ =
  (BE2¬2BE (f , fp) 0≡∣f∣2¬) , (BE2¬2BE (g , gp) 0≡∣g∣2¬)
  where
    0≡∣f∣2¬ = sym (m+n≡0⇒m≡0 (∣ f ∣2¬) {∣ g ∣2¬} (sym 0≡∣f∧g∣2¬))
    0≡∣g∣2¬ = sym (m+n≡0⇒n≡0 (∣ f ∣2¬) {∣ g ∣2¬} (sym 0≡∣f∧g∣2¬))
BE2¬2BE ((V x ⇒ ⊥) ⇒ ⊥ , fp) ()
BE2¬2BE ((V x ⇒ ⊥) ⇒ V x₁ , ())
BE2¬2BE ((V x ⇒ ⊥) ⇒ (f₁ ∧ f₂) , ())
BE2¬2BE ((V x ⇒ ⊥) ⇒ (f₁ ∨ f₂) , ())
BE2¬2BE ((V x ⇒ ⊥) ⇒ f₁ ⇒ f₂ , ())

-- convert head expressions with double negation to head expression ------------
-- if a head expression with double negation does not contain double
-- negation, it is a head expression
HE2¬2HE : ((f , _) : HE2¬) → (0 ≡ ∣ f ∣2¬) → isHE f
HE2¬2HE (⊥ , tt) _ = tt
HE2¬2HE (V x , tt) _ = tt
HE2¬2HE (V x ⇒ ⊥ , tt) _ = tt
HE2¬2HE (f ∨ g , (fp , gp)) 0≡∣f∨g∣2¬ =
  (HE2¬2HE (f , fp) 0≡∣f∣2¬) , (HE2¬2HE (g , gp) 0≡∣g∣2¬)
  where
    0≡∣f∣2¬ = sym (m+n≡0⇒m≡0 (∣ f ∣2¬) {∣ g ∣2¬} (sym 0≡∣f∨g∣2¬))
    0≡∣g∣2¬ = sym (m+n≡0⇒n≡0 (∣ f ∣2¬) {∣ g ∣2¬} (sym 0≡∣f∨g∣2¬))
HE2¬2HE ((V x ⇒ ⊥) ⇒ ⊥ , fp) ()
HE2¬2HE ((V x ⇒ ⊥) ⇒ V x₁ , ())
HE2¬2HE ((V x ⇒ ⊥) ⇒ (f₁ ∧ f₂) , ())
HE2¬2HE ((V x ⇒ ⊥) ⇒ (f₁ ∨ f₂) , ())
HE2¬2HE ((V x ⇒ ⊥) ⇒ f₁ ⇒ f₂ , ())

-- reordering body expressions with double negation ----------------------------
-- every body expression that contains at least one double negation
-- can be rewritten as the conjunction of a body expression
-- and a negated atom
reorder-BE2¬ : (f : F) → isBE2¬ f → {n : ℕ} → {suc n ≡ ∣ f ∣2¬} →
               Σ[ ((ϕ , _) , a) ∈ (BE2¬ × Var) ]
               ((f ≡HT (ϕ ∧ (¬ (¬ (V a))))) × (n ≡ ∣ ϕ ∣2¬))
reorder-BE2¬ (((V a) ⇒ ⊥) ⇒ ⊥) tt {0} {refl} =
  ((⊤ , tt) , a) , (symm⇔ ⊤-lid-∧ , refl)

reorder-BE2¬ (f ∧ g) (fp , gp) {n} {sn≡∣f∧g∣2¬} with ∣ f ∣2¬×≡
-- f contains no double negation
... | 0 , 0≡∣f∣2¬ = (((f ∧ ψ) , (fp , ψp)) , a) , (proof , n≡∣f∧ψ∣2¬)
  where
    -- then g contains all sn double negations
    -- and g can be rewritten by recursion
    ih : Σ[ ((ϕ , _) , a) ∈ (BE2¬ × Var) ]
         ((g ≡HT (ϕ ∧ (¬ (¬ (V a))))) × (n ≡ ∣ ϕ ∣2¬))
    ih = reorder-BE2¬ g gp {n} {x≡y+z∧0≡y⇒x≡z sn≡∣f∧g∣2¬ 0≡∣f∣2¬}

    ψ  = p1 (p1 (p1 ih))
    ψp = p2 (p1 (p1 ih))
    a  = p2 (p1 ih)
    g⇔ψ∧¬¬a = p1 (p2 ih)
    n≡∣ψ∣2¬ = p2 (p2 ih)

    proof =
      f ∧ g                   ≡HT⟨ replace∧rhs g⇔ψ∧¬¬a ⟩
      f ∧ (ψ ∧ (¬ (¬ (V a)))) ≡HT⟨ assoc∧ ⟩ˢ
      (f ∧ ψ) ∧ (¬ (¬ (V a))) ■

    n≡∣f∧ψ∣2¬ = 0≡y∧x≡z⇒x≡y+z 0≡∣f∣2¬ n≡∣ψ∣2¬

-- f contains sm double negation (i.e. at least one)
... | suc m , sm≡∣f∣2¬ = (((g ∧ ψ) , (gp , ψp)) , a) , (proof , n≡∣g∧ψ∣2¬)
  where
    -- recursion on f
    ih : Σ[ ((ϕ , _) , a) ∈ (BE2¬ × Var) ]
         ((f ≡HT (ϕ ∧ (¬ (¬ (V a))))) × (m ≡ ∣ ϕ ∣2¬))
    ih = reorder-BE2¬ f fp {m} {sm≡∣f∣2¬}

    ψ  = p1 (p1 (p1 ih))
    ψp = p2 (p1 (p1 ih))
    a  = p2 (p1 ih)
    f⇔ψ∧a = p1 (p2 ih)
    m≡∣ϕ∣2¬ = p2 (p2 ih)

    proof =
      f ∧ g                   ≡HT⟨ comm∧ ⟩
      g ∧ f                   ≡HT⟨ replace∧rhs f⇔ψ∧a ⟩
      g ∧ (ψ ∧ (¬ (¬ (V a)))) ≡HT⟨ assoc∧ ⟩ˢ
      (g ∧ ψ) ∧ (¬ (¬ (V a))) ■

    n≡∣g∧ψ∣2¬ = sn≡a+b∧sm≡a∧m≡c⇒n≡b+c sn≡∣f∧g∣2¬ sm≡∣f∣2¬ m≡∣ϕ∣2¬

-- absurd cases
reorder-BE2¬ (⊥ ⇒ ⊥) p {n} {()}
reorder-BE2¬ (⊥ ⇒ V x) ()
reorder-BE2¬ (⊥ ⇒ (f₁ ∧ f₂)) ()
reorder-BE2¬ (⊥ ⇒ (f₁ ∨ f₂)) ()
reorder-BE2¬ (⊥ ⇒ f₁ ⇒ f₂) ()
reorder-BE2¬ (V x ⇒ ⊥) p {n} {()}
reorder-BE2¬ (V x ⇒ V x₁) ()
reorder-BE2¬ (V x ⇒ (f₁ ∧ f₂)) ()
reorder-BE2¬ (V x ⇒ (f₁ ∨ f₂)) ()
reorder-BE2¬ (V x ⇒ f₁ ⇒ f₂) ()

-- reordering head expressions with double negation ----------------------------
-- every head expression that contains at least one double negation
-- can be rewritten as the disjunction of a head expression
-- and a negated atom
reorder-HE2¬ : (f : F) → isHE2¬ f → {n : ℕ} → {suc n ≡ ∣ f ∣2¬} →
               Σ[ ((ϕ , _) , a) ∈ (HE2¬ × Var) ]
               ((f ≡HT (ϕ ∨ (¬ (¬ (V a))))) × (n ≡ ∣ ϕ ∣2¬))
reorder-HE2¬ (((V a) ⇒ ⊥) ⇒ ⊥) tt {0} {refl} =
  ((⊥ , tt) , a) , (symm⇔ ⊥-lid-∨ , refl)

reorder-HE2¬ (f ∨ g) (fp , gp) {n} {sn≡∣f∨g∣2¬} with ∣ f ∣2¬×≡
-- f contains no double negation
... | 0 , 0≡∣f∣2¬ = (((f ∨ ψ) , (fp , ψp)) , a) , (proof , n≡∣f∨ψ∣2¬)
  where
    -- then g contains all sn double negations
    -- and g can be rewritten by recursion
    ih : Σ[ ((ϕ , _) , a) ∈ (HE2¬ × Var) ]
         ((g ≡HT (ϕ ∨ (¬ (¬ (V a))))) × (n ≡ ∣ ϕ ∣2¬))
    ih = reorder-HE2¬ g gp {n} {x≡y+z∧0≡y⇒x≡z sn≡∣f∨g∣2¬ 0≡∣f∣2¬}

    ψ  = p1 (p1 (p1 ih))
    ψp = p2 (p1 (p1 ih))
    a  = p2 (p1 ih)
    g⇔ψ∨¬¬a = p1 (p2 ih)
    n≡∣ψ∣2¬ = p2 (p2 ih)

    proof =
      f ∨ g                   ≡HT⟨ replace∨rhs g⇔ψ∨¬¬a ⟩
      f ∨ (ψ ∨ (¬ (¬ (V a)))) ≡HT⟨ assoc∨ ⟩ˢ
      (f ∨ ψ) ∨ (¬ (¬ (V a))) ■

    n≡∣f∨ψ∣2¬ = 0≡y∧x≡z⇒x≡y+z  0≡∣f∣2¬ n≡∣ψ∣2¬

-- f contains sm double negation (i.e. at least one)
... | suc m , sm≡∣f∣2¬ = (((g ∨ ψ) , (gp , ψp)) , a) , (proof , n≡∣g∨ψ∣2¬)
  where
    -- recursion on f
    ih : Σ[ ((ϕ , _) , a) ∈ (HE2¬ × Var) ]
         ((f ≡HT (ϕ ∨ (¬ (¬ (V a))))) × (m ≡ ∣ ϕ ∣2¬))
    ih = reorder-HE2¬ f fp {m} {sm≡∣f∣2¬}

    ψ  = p1 (p1 (p1 ih))
    ψp = p2 (p1 (p1 ih))
    a  = p2 (p1 ih)
    f⇔ψ∨a = p1 (p2 ih)
    m≡∣ψ∣2¬ = p2 (p2 ih)

    proof =
      f ∨ g                   ≡HT⟨ comm∨ ⟩
      g ∨ f                   ≡HT⟨ replace∨rhs f⇔ψ∨a ⟩
      g ∨ (ψ ∨ (¬ (¬ (V a)))) ≡HT⟨ assoc∨ ⟩ˢ
      (g ∨ ψ) ∨ (¬ (¬ (V a))) ■

    n≡∣g∨ψ∣2¬ = sn≡a+b∧sm≡a∧m≡c⇒n≡b+c sn≡∣f∨g∣2¬ sm≡∣f∣2¬ m≡∣ψ∣2¬

-- absurd cases
reorder-HE2¬ (⊥ ⇒ ⊥) p {n} {()}
reorder-HE2¬ (⊥ ⇒ V x) ()
reorder-HE2¬ (⊥ ⇒ (f₁ ∧ f₂)) ()
reorder-HE2¬ (⊥ ⇒ (f₁ ∨ f₂)) ()
reorder-HE2¬ (⊥ ⇒ f₁ ⇒ f₂) ()
reorder-HE2¬ (V x ⇒ ⊥) p {n} {()}
reorder-HE2¬ (V x ⇒ V x₁) ()
reorder-HE2¬ (V x ⇒ (f₁ ∧ f₂)) ()
reorder-HE2¬ (V x ⇒ (f₁ ∨ f₂)) ()
reorder-HE2¬ (V x ⇒ f₁ ⇒ f₂) ()

-- remove all double negation in a rule body -----------------------------------
remove-2¬-body : ((r , p) : R2¬) → {n : ℕ} → {n ≡ ∣ (r , p) ∣B2¬} →
                 Σ[ ((ϕ , _) , (ψ , _)) ∈ (BE × HE2¬) ] (r ≡HT (ϕ ⇒ ψ))
remove-2¬-body (b ⇒ h , (bp , hp)) {0} {0≡∣b∣2¬} =
  ((b , BE2¬2BE (b , bp) 0≡∣b∣2¬) , (h , hp)) , refl⇔

remove-2¬-body (b ⇒ h , (bp , hp)) {suc n} {sn≡∣b∣2¬} =
  ((ϕ , ϕp) , (ψ , ψp)) , proof
  where
    -- rewrite b as ϕ' ∧ ¬¬a
    rw-b : Σ[ ((ϕ , _) , a) ∈ (BE2¬ × Var) ]
           ((b ≡HT (ϕ ∧ (¬ (¬ (V a))))) × (n ≡ ∣ ϕ ∣2¬))
    rw-b = reorder-BE2¬ b bp {n} {sn≡∣b∣2¬}

    ϕ'  = p1 (p1 (p1 rw-b))
    ϕ'p = p2 (p1 (p1 rw-b))
    a   = p2 (p1 rw-b)
    b⇔ϕ'∧¬¬a = p1 (p2 rw-b)
    n≡∣ϕ'∣2¬ = p2 (p2 rw-b)

    ψ' = h ∨ (¬ (V a))

    rm-ϕ' : Σ[ ((ϕ , _) , (ψ , _)) ∈ (BE × HE2¬) ] ((ϕ' ⇒ ψ') ≡HT (ϕ ⇒ ψ))
    rm-ϕ' = remove-2¬-body ((ϕ' ⇒ ψ') , (ϕ'p , (hp , tt))) {n} {n≡∣ϕ'∣2¬}

    ϕ  = p1 (p1 (p1 rm-ϕ'))
    ϕp = p2 (p1 (p1 rm-ϕ'))
    ψ  = p1 (p2 (p1 rm-ϕ'))
    ψp = p2 (p2 (p1 rm-ϕ'))
    ϕ'⇒ψ'⇔ϕ⇒ψ = p2 rm-ϕ'

    proof : (b ⇒ h) ≡HT (ϕ ⇒ ψ)
    proof =
      b ⇒ h                    ≡HT⟨ replace⇒lhs b⇔ϕ'∧¬¬a ⟩
      (ϕ' ∧ (¬ (¬ (V a)))) ⇒ h ≡HT⟨ rem2¬body ⟩
      ϕ' ⇒ (h ∨ (¬ (V a)))     ≡HT⟨def⟩
      ϕ' ⇒ ψ'                  ≡HT⟨ ϕ'⇒ψ'⇔ϕ⇒ψ ⟩
      ϕ ⇒ ψ                    ■

-- remove all double negation in a rule head -----------------------------------
remove-2¬-head : ((b , _) : BE) → ((h , _) : HE2¬) → {n : ℕ} → {n ≡ ∣ h ∣2¬} →
                 Σ[ ((ϕ , _) , (ψ , _)) ∈ (BE × HE) ] ((b ⇒ h) ≡HT (ϕ ⇒ ψ))
remove-2¬-head (b , bp) (h , hp) {0} {0≡∣h∣2¬} =
  ((b , bp) , (h , HE2¬2HE (h , hp) 0≡∣h∣2¬)) , refl⇔

remove-2¬-head (b , bp) (h , hp) {suc n} {sn≡∣h∣2¬} =
  ((ϕ , ϕp) , (ψ , ψp)) , proof
  where
    -- rewrite h as ψ' ∧ ¬¬a
    rw-h : Σ[ ((ϕ , _) , a) ∈ (HE2¬ × Var) ]
           ((h ≡HT (ϕ ∨ (¬ (¬ (V a))))) × (n ≡ ∣ ϕ ∣2¬))
    rw-h = reorder-HE2¬ h hp {n} {sn≡∣h∣2¬}

    ψ'  = p1 (p1 (p1 rw-h))
    ψ'p = p2 (p1 (p1 rw-h))
    a   = p2 (p1 rw-h)
    h⇔ψ'∨¬¬a = p1 (p2 rw-h)
    n≡∣ψ'∣2¬ = p2 (p2 rw-h)

    ϕ' = b ∧ (¬ (V a))

    rm-ψ' : Σ[ ((ϕ , _) , (ψ , _)) ∈ (BE × HE) ] ((ϕ' ⇒ ψ') ≡HT (ϕ ⇒ ψ))
    rm-ψ' = remove-2¬-head (ϕ' , (bp , tt)) (ψ' , ψ'p) {n} {n≡∣ψ'∣2¬}

    ϕ  = p1 (p1 (p1 rm-ψ'))
    ϕp = p2 (p1 (p1 rm-ψ'))
    ψ  = p1 (p2 (p1 rm-ψ'))
    ψp = p2 (p2 (p1 rm-ψ'))
    ϕ'⇒ψ'⇔ϕ⇒ψ = p2 rm-ψ'

    proof : (b ⇒ h) ≡HT (ϕ ⇒ ψ)
    proof =
      b ⇒ h                    ≡HT⟨ replace⇒rhs h⇔ψ'∨¬¬a ⟩
      b ⇒ (ψ' ∨ (¬ (¬ (V a)))) ≡HT⟨ rem2¬head ⟩
      (b ∧ (¬ (V a))) ⇒ ψ'     ≡HT⟨def⟩
      ϕ' ⇒ ψ'                  ≡HT⟨ ϕ'⇒ψ'⇔ϕ⇒ψ ⟩
      ϕ ⇒ ψ                    ■
