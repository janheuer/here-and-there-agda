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
∣_∣2¬×≡ : (f : F) → Σ ℕ (λ n → n ≡ ∣ f ∣2¬)
∣ f ∣2¬×≡ = ∣ f ∣2¬ , refl

-- reordering body expressions with double negation ----------------------------
-- every body expression that contains at least one double negation
-- can be rewritten as the conjunction of a body expression
-- and a negated atom
reorder-BE2¬ : (f : F) → isBE2¬ f → {n : ℕ} → {suc n ≡ ∣ f ∣2¬} →
               Σ (BE2¬ × Var) (λ (ϕ , a) → f ≡HT ((be2¬f ϕ) ∧ (¬ (¬ (V a)))))
reorder-BE2¬ (((V a) ⇒ ⊥) ⇒ ⊥) tt {0} {refl} =
  (be2¬ ⊤ tt , a) , symm⇔ ⊤-lid-∧

reorder-BE2¬ (f ∧ g) (fp , gp) {n} {sn≡∣f∧g∣2¬} with ∣ f ∣2¬×≡
-- f contains no double negation
... | 0 , 0≡∣f∣2¬ = (be2¬ (f ∧ (be2¬f ψ)) (fp , (be2¬p ψ)) , a) , proof
  where
    -- then g contains all sn double negations
    -- and g can be rewritten by recursion
    ih : Σ (BE2¬ × Var) (λ (ϕ , a) → g ≡HT ((be2¬f ϕ) ∧ (¬ (¬ (V a)))))
    ih = reorder-BE2¬ g gp {n} {h sn≡∣f∧g∣2¬ 0≡∣f∣2¬}
      where
        h : {x y z : ℕ} → x ≡ y + z → 0 ≡ y → x ≡ z
        h refl refl = refl

    ψ = p1 (p1 ih)
    a = p2 (p1 ih)
    f⇔ψ∧a = p2 ih

    proof =
      f ∧ g                           ≡HT⟨ replace∧rhs f⇔ψ∧a ⟩
      f ∧ ((be2¬f ψ) ∧ (¬ (¬ (V a)))) ≡HT⟨ assoc∧ ⟩ˢ
      (f ∧ (be2¬f ψ)) ∧ (¬ (¬ (V a))) ■

-- f contains sm double negation (i.e. at least one)
... | suc m , sm≡∣f∣2¬ = (be2¬ (g ∧ (be2¬f ψ)) (gp , (be2¬p ψ)) , a) , proof
  where
    -- recursion on f
    ih : Σ (BE2¬ × Var) (λ (ϕ , a) → f ≡HT ((be2¬f ϕ) ∧ (¬ (¬ (V a)))))
    ih = reorder-BE2¬ f fp {m} {sm≡∣f∣2¬}

    ψ = p1 (p1 ih)
    a = p2 (p1 ih)
    f⇔ψ∧a = p2 ih

    proof =
      f ∧ g                           ≡HT⟨ comm∧ ⟩
      g ∧ f                           ≡HT⟨ replace∧rhs f⇔ψ∧a ⟩
      g ∧ ((be2¬f ψ) ∧ (¬ (¬ (V a)))) ≡HT⟨ assoc∧ ⟩ˢ
      (g ∧ (be2¬f ψ)) ∧ (¬ (¬ (V a))) ■

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
               Σ (HE2¬ × Var) (λ (ϕ , a) → f ≡HT ((he2¬f ϕ) ∨ (¬ (¬ (V a)))))
reorder-HE2¬ (((V a) ⇒ ⊥) ⇒ ⊥) tt {0} {refl} =
  (he2¬ ⊥ tt , a) , symm⇔ ⊥-lid-∨

reorder-HE2¬ (f ∨ g) (fp , gp) {n} {sn≡∣f∨g∣2¬} with ∣ f ∣2¬×≡
-- f contains no double negation
... | 0 , 0≡∣f∣2¬ = (he2¬ (f ∨ (he2¬f ψ)) (fp , (he2¬p ψ)) , a) , proof
  where
    -- then g contains all sn double negations
    -- and g can be rewritten by recursion
    ih : Σ (HE2¬ × Var) (λ (ϕ , a) → g ≡HT ((he2¬f ϕ) ∨ (¬ (¬ (V a)))))
    ih = reorder-HE2¬ g gp {n} {h sn≡∣f∨g∣2¬ 0≡∣f∣2¬}
      where
        h : {x y z : ℕ} → x ≡ y + z → 0 ≡ y → x ≡ z
        h refl refl = refl

    ψ = p1 (p1 ih)
    a = p2 (p1 ih)
    f⇔ψ∨a = p2 ih

    proof =
      f ∨ g                           ≡HT⟨ replace∨rhs f⇔ψ∨a ⟩
      f ∨ ((he2¬f ψ) ∨ (¬ (¬ (V a)))) ≡HT⟨ assoc∨ ⟩ˢ
      (f ∨ (he2¬f ψ)) ∨ (¬ (¬ (V a))) ■

-- f contains sm double negation (i.e. at least one)
... | suc m , sm≡∣f∣2¬ = (he2¬ (g ∨ (he2¬f ψ)) (gp , (he2¬p ψ)) , a) , proof
  where
    -- recursion on f
    ih : Σ (HE2¬ × Var) (λ (ϕ , a) → f ≡HT ((he2¬f ϕ) ∨ (¬ (¬ (V a)))))
    ih = reorder-HE2¬ f fp {m} {sm≡∣f∣2¬}

    ψ = p1 (p1 ih)
    a = p2 (p1 ih)
    f⇔ψ∨a = p2 ih

    proof =
      f ∨ g                           ≡HT⟨ comm∨ ⟩
      g ∨ f                           ≡HT⟨ replace∨rhs f⇔ψ∨a ⟩
      g ∨ ((he2¬f ψ) ∨ (¬ (¬ (V a)))) ≡HT⟨ assoc∨ ⟩ˢ
      (g ∨ (he2¬f ψ)) ∨ (¬ (¬ (V a))) ■

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

