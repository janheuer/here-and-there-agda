module HereAndThere.DoubleNegation where

open import Data.Nat using (_+_ ; suc)

open import HereAndThere
open import HereAndThere.NestedLogicPrograms
open import Formula.LogicPrograms
open import Formula.LogicPrograms.Nested
open import Formula.LogicPrograms.DoubleNegation

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

∣_∣B2¬×≡ : (r : R2¬) → Σ[ n ∈ ℕ ] (n ≡ ∣ r ∣B2¬)
∣ r ∣B2¬×≡ = ∣ r ∣B2¬ , refl

-- number of double negations in a rule head
∣_∣H2¬ : R2¬ → ℕ
∣ (b ⇒ h) , _ ∣H2¬ = ∣ h ∣2¬

∣_∣H2¬×≡ : (r : R2¬) → Σ[ n ∈ ℕ ] (n ≡ ∣ r ∣H2¬)
∣ r ∣H2¬×≡ = ∣ r ∣H2¬ , refl

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
    h : {n m : ℕ} → 0 ≡ n + m → (0 ≡ n) × (0 ≡ m)
    h {0} {0} refl = refl , refl

    0≡∣f∣2¬ = p1 (h {∣ f ∣2¬} {∣ g ∣2¬} 0≡∣f∧g∣2¬)
    0≡∣g∣2¬ = p2 (h {∣ f ∣2¬} {∣ g ∣2¬} 0≡∣f∧g∣2¬)
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
HE2¬2HE (f ∨ g , (fp , gp)) 0≡∣f∧g∣2¬ =
  (HE2¬2HE (f , fp) 0≡∣f∣2¬) , (HE2¬2HE (g , gp) 0≡∣g∣2¬)
  where
    h : {n m : ℕ} → 0 ≡ n + m → (0 ≡ n) × (0 ≡ m)
    h {0} {0} refl = refl , refl

    0≡∣f∣2¬ = p1 (h {∣ f ∣2¬} {∣ g ∣2¬} 0≡∣f∧g∣2¬)
    0≡∣g∣2¬ = p2 (h {∣ f ∣2¬} {∣ g ∣2¬} 0≡∣f∧g∣2¬)
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
    ih = reorder-BE2¬ g gp {n} {h sn≡∣f∧g∣2¬ 0≡∣f∣2¬}
      where
        h : {x y z : ℕ} → x ≡ y + z → 0 ≡ y → x ≡ z
        h refl refl = refl

    ψ  = p1 (p1 (p1 ih))
    ψp = p2 (p1 (p1 ih))
    -- ψ = p1 (p1 ih)
    a = p2 (p1 ih)
    f⇔ψ∧a = p1 (p2 ih)

    proof =
      f ∧ g                   ≡HT⟨ replace∧rhs f⇔ψ∧a ⟩
      f ∧ (ψ ∧ (¬ (¬ (V a)))) ≡HT⟨ assoc∧ ⟩ˢ
      (f ∧ ψ) ∧ (¬ (¬ (V a))) ■

    n≡∣f∧ψ∣2¬ = h 0≡∣f∣2¬ (p2 (p2 ih))
      where
        h : {x y z : ℕ} → 0 ≡ y → x ≡ z → x ≡ y + z
        h refl refl = refl

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

    proof =
      f ∧ g                   ≡HT⟨ comm∧ ⟩
      g ∧ f                   ≡HT⟨ replace∧rhs f⇔ψ∧a ⟩
      g ∧ (ψ ∧ (¬ (¬ (V a)))) ≡HT⟨ assoc∧ ⟩ˢ
      (g ∧ ψ) ∧ (¬ (¬ (V a))) ■

    open import Data.Nat
    open import Data.Nat.Properties
    open import Relation.Binary.PropositionalEquality.Core as Eq
    open Eq.≡-Reasoning

    n≡∣g∧ψ∣2¬ =
      n                       ≡⟨⟩
      (suc n) ∸ 1             ≡⟨ cong (λ (n : ℕ) → n ∸ 1) sn≡∣f∧g∣2¬ ⟩
      (∣ f ∧ g ∣2¬) ∸ 1       ≡⟨⟩
      (∣ f ∣2¬ + ∣ g ∣2¬) ∸ 1 ≡⟨ cong (λ (n : ℕ) → n ∸ 1) (+-comm (∣ f ∣2¬) (∣ g ∣2¬)) ⟩
      (∣ g ∣2¬ + ∣ f ∣2¬) ∸ 1 ≡⟨ cong (λ (n : ℕ) → (∣ g ∣2¬ + n) ∸ 1) (sym sm≡∣f∣2¬) ⟩
      (∣ g ∣2¬ + (suc m)) ∸ 1 ≡⟨ +-∸-assoc ∣ g ∣2¬ {suc m} {1} (h m) ⟩
      ∣ g ∣2¬ + (suc m ∸ 1)   ≡⟨⟩
      ∣ g ∣2¬ + m             ≡⟨ cong (λ (n : ℕ) → ∣ g ∣2¬ + n) (p2 (p2 ih)) ⟩
      ∣ g ∣2¬ + ∣ ψ ∣2¬       ≡⟨⟩
      ∣ g ∧ ψ ∣2¬             ∎
      where
        h : (n : ℕ) → 1 Data.Nat.≤ suc n
        h zero = ≤-reflexive refl
        h (suc n) = ≤-step (h n)

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
               Σ[ ((ϕ , _) , a) ∈ (HE2¬ × Var) ] (f ≡HT (ϕ ∨ (¬ (¬ (V a)))))
reorder-HE2¬ (((V a) ⇒ ⊥) ⇒ ⊥) tt {0} {refl} =
  ((⊥ , tt) , a) , symm⇔ ⊥-lid-∨

reorder-HE2¬ (f ∨ g) (fp , gp) {n} {sn≡∣f∨g∣2¬} with ∣ f ∣2¬×≡
-- f contains no double negation
... | 0 , 0≡∣f∣2¬ = (((f ∨ ψ) , (fp , ψp)) , a) , proof
  where
    -- then g contains all sn double negations
    -- and g can be rewritten by recursion
    ih : Σ[ ((ϕ , _) , a) ∈ (HE2¬ × Var) ] (g ≡HT (ϕ ∨ (¬ (¬ (V a)))))
    ih = reorder-HE2¬ g gp {n} {h sn≡∣f∨g∣2¬ 0≡∣f∣2¬}
      where
        h : {x y z : ℕ} → x ≡ y + z → 0 ≡ y → x ≡ z
        h refl refl = refl

    x = p1 (p1 ih)
    ψ = p1 x
    ψp = p2 x
    a = p2 (p1 ih)
    f⇔ψ∨a = p2 ih

    proof =
      f ∨ g                   ≡HT⟨ replace∨rhs f⇔ψ∨a ⟩
      f ∨ (ψ ∨ (¬ (¬ (V a)))) ≡HT⟨ assoc∨ ⟩ˢ
      (f ∨ ψ) ∨ (¬ (¬ (V a))) ■

-- f contains sm double negation (i.e. at least one)
... | suc m , sm≡∣f∣2¬ = (((g ∨ ψ) , (gp , ψp)) , a) , proof
  where
    -- recursion on f
    ih : Σ[ ((ϕ , _) , a) ∈ (HE2¬ × Var) ] (f ≡HT (ϕ ∨ (¬ (¬ (V a)))))
    ih = reorder-HE2¬ f fp {m} {sm≡∣f∣2¬}

    x = p1 (p1 ih)
    ψ = p1 x
    ψp = p2 x
    a = p2 (p1 ih)
    f⇔ψ∨a = p2 ih

    proof =
      f ∨ g                   ≡HT⟨ comm∨ ⟩
      g ∨ f                   ≡HT⟨ replace∨rhs f⇔ψ∨a ⟩
      g ∨ (ψ ∨ (¬ (¬ (V a)))) ≡HT⟨ assoc∨ ⟩ˢ
      (g ∨ ψ) ∨ (¬ (¬ (V a))) ■

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

