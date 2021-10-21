module HereAndThere.LogicPrograms.DoubleNegation where

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
-- every body expression f that contains at least one double negation
-- can be rewritten as the conjunction of a body expression ϕ
-- and a double negated atom a
-- f ⇔ to ϕ ∧ ¬¬a
reorder-BE2¬ : (f : F) → isBE2¬ f → {n : ℕ} → {suc n ≡ ∣ f ∣2¬} →
               Σ[ ((ϕ , _) , a) ∈ (BE2¬ × Var) ]
               ((f ≡HT (ϕ ∧ (¬ (¬ (V a))))) × (n ≡ ∣ ϕ ∣2¬))

reorder-BE2¬ (((V a) ⇒ ⊥) ⇒ ⊥) tt {0} {refl} =
  ((⊤ , tt) , a) , (symm⇔ ⊤-lid-∧ , refl)

reorder-BE2¬ (f ∧ g) (fp , gp) {n} {sn≡∣f∧g∣2¬} with ∣ f ∣2¬×≡
-- f contains no double negation
... | 0 , 0≡∣f∣2¬ = (((f ∧ ϕ) , (fp , ϕp)) , a) , (proof , n≡∣f∧ϕ∣2¬)
  where
    -- then g contains all sn double negations
    -- and g can be rewritten by recursion
    ih : Σ[ ((ϕ , ϕp) , a) ∈ (BE2¬ × Var) ]
         ((g ≡HT (ϕ ∧ (¬ (¬ (V a))))) × (n ≡ ∣ ϕ ∣2¬))
    ih = reorder-BE2¬ g gp {n} {x≡y+z∧0≡y⇒x≡z sn≡∣f∧g∣2¬ 0≡∣f∣2¬}

    ϕ  = p1 (p1 (p1 ih))
    ϕp = p2 (p1 (p1 ih))
    a  = p2 (p1 ih)
    g⇔ϕ∧¬¬a = p1 (p2 ih)
    n≡∣ϕ∣2¬ = p2 (p2 ih)

    proof =
      f ∧ g                   ≡HT⟨ replace∧rhs g⇔ϕ∧¬¬a ⟩
      f ∧ (ϕ ∧ (¬ (¬ (V a)))) ≡HT⟨ assoc∧ ⟩ˢ
      (f ∧ ϕ) ∧ (¬ (¬ (V a))) ■

    n≡∣f∧ϕ∣2¬ = 0≡y∧x≡z⇒x≡y+z 0≡∣f∣2¬ n≡∣ϕ∣2¬

-- f contains sm double negation (i.e. at least one)
... | suc m , sm≡∣f∣2¬ = (((g ∧ ϕ) , (gp , ϕp)) , a) , (proof , n≡∣g∧ϕ∣2¬)
  where
    -- recursion on f
    ih : Σ[ ((ϕ , ϕp) , a) ∈ (BE2¬ × Var) ]
         ((f ≡HT (ϕ ∧ (¬ (¬ (V a))))) × (m ≡ ∣ ϕ ∣2¬))
    ih = reorder-BE2¬ f fp {m} {sm≡∣f∣2¬}

    ϕ  = p1 (p1 (p1 ih))
    ϕp = p2 (p1 (p1 ih))
    a  = p2 (p1 ih)
    f⇔ϕ∧a = p1 (p2 ih)
    m≡∣ϕ∣2¬ = p2 (p2 ih)

    proof =
      f ∧ g                   ≡HT⟨ comm∧ ⟩
      g ∧ f                   ≡HT⟨ replace∧rhs f⇔ϕ∧a ⟩
      g ∧ (ϕ ∧ (¬ (¬ (V a)))) ≡HT⟨ assoc∧ ⟩ˢ
      (g ∧ ϕ) ∧ (¬ (¬ (V a))) ■

    n≡∣g∧ϕ∣2¬ = sn≡a+b∧sm≡a∧m≡c⇒n≡b+c sn≡∣f∧g∣2¬ sm≡∣f∣2¬ m≡∣ϕ∣2¬

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
-- every head expression f that contains at least one double negation
-- can be rewritten as the disjunction of a head expression ϕ
-- and a double negated atom a
-- f ⇔ ϕ ∨ ¬¬a
reorder-HE2¬ : (f : F) → isHE2¬ f → {n : ℕ} → {suc n ≡ ∣ f ∣2¬} →
               Σ[ ((ϕ , _) , a) ∈ (HE2¬ × Var) ]
               ((f ≡HT (ϕ ∨ (¬ (¬ (V a))))) × (n ≡ ∣ ϕ ∣2¬))

reorder-HE2¬ (((V a) ⇒ ⊥) ⇒ ⊥) tt {0} {refl} =
  ((⊥ , tt) , a) , (symm⇔ ⊥-lid-∨ , refl)

reorder-HE2¬ (f ∨ g) (fp , gp) {n} {sn≡∣f∨g∣2¬} with ∣ f ∣2¬×≡
-- f contains no double negation
... | 0 , 0≡∣f∣2¬ = (((f ∨ ϕ) , (fp , ϕp)) , a) , (proof , n≡∣f∨ϕ∣2¬)
  where
    -- then g contains all sn double negations
    -- and g can be rewritten by recursion
    ih : Σ[ ((ϕ , ϕp) , a) ∈ (HE2¬ × Var) ]
         ((g ≡HT (ϕ ∨ (¬ (¬ (V a))))) × (n ≡ ∣ ϕ ∣2¬))
    ih = reorder-HE2¬ g gp {n} {x≡y+z∧0≡y⇒x≡z sn≡∣f∨g∣2¬ 0≡∣f∣2¬}

    ϕ  = p1 (p1 (p1 ih))
    ϕp = p2 (p1 (p1 ih))
    a  = p2 (p1 ih)
    g⇔ϕ∨¬¬a = p1 (p2 ih)
    n≡∣ϕ∣2¬ = p2 (p2 ih)

    proof =
      f ∨ g                   ≡HT⟨ replace∨rhs g⇔ϕ∨¬¬a ⟩
      f ∨ (ϕ ∨ (¬ (¬ (V a)))) ≡HT⟨ assoc∨ ⟩ˢ
      (f ∨ ϕ) ∨ (¬ (¬ (V a))) ■

    n≡∣f∨ϕ∣2¬ = 0≡y∧x≡z⇒x≡y+z  0≡∣f∣2¬ n≡∣ϕ∣2¬

-- f contains sm double negation (i.e. at least one)
... | suc m , sm≡∣f∣2¬ = (((g ∨ ϕ) , (gp , ϕp)) , a) , (proof , n≡∣g∨ϕ∣2¬)
  where
    -- recursion on f
    ih : Σ[ ((ϕ , ϕp) , a) ∈ (HE2¬ × Var) ]
         ((f ≡HT (ϕ ∨ (¬ (¬ (V a))))) × (m ≡ ∣ ϕ ∣2¬))
    ih = reorder-HE2¬ f fp {m} {sm≡∣f∣2¬}

    ϕ  = p1 (p1 (p1 ih))
    ϕp = p2 (p1 (p1 ih))
    a  = p2 (p1 ih)
    f⇔ϕ∨a = p1 (p2 ih)
    m≡∣ϕ∣2¬ = p2 (p2 ih)

    proof =
      f ∨ g                   ≡HT⟨ comm∨ ⟩
      g ∨ f                   ≡HT⟨ replace∨rhs f⇔ϕ∨a ⟩
      g ∨ (ϕ ∨ (¬ (¬ (V a)))) ≡HT⟨ assoc∨ ⟩ˢ
      (g ∨ ϕ) ∨ (¬ (¬ (V a))) ■

    n≡∣g∨ϕ∣2¬ = sn≡a+b∧sm≡a∧m≡c⇒n≡b+c sn≡∣f∨g∣2¬ sm≡∣f∣2¬ m≡∣ϕ∣2¬

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
-- every rule r with double negation can be rewritten as the implication
-- of a body expression ϕ (without double negation) and a head expression ψ
-- with double negation
-- r ⇔ ϕ ⇒ ψ
remove-2¬-body : ((r , p) : R2¬) → {n : ℕ} → {n ≡ ∣ (r , p) ∣B2¬} →
                 Σ[ ((ϕ , _) , (ψ , _)) ∈ (BE × HE2¬) ] (r ≡HT (ϕ ⇒ ψ))

remove-2¬-body (b ⇒ h , (bp , hp)) {0} {0≡∣b∣2¬} =
  ((b , BE2¬2BE (b , bp) 0≡∣b∣2¬) , (h , hp)) , refl⇔

remove-2¬-body (b ⇒ h , (bp , hp)) {suc n} {sn≡∣b∣2¬} =
  ((ϕ , ϕp) , (ψ , ψp)) , proof
  where
    -- rewrite b as ϕ' ∧ ¬¬a
    rw-b : Σ[ ((ϕ' , ϕ'p) , a) ∈ (BE2¬ × Var) ]
           ((b ≡HT (ϕ' ∧ (¬ (¬ (V a))))) × (n ≡ ∣ ϕ' ∣2¬))
    rw-b = reorder-BE2¬ b bp {n} {sn≡∣b∣2¬}

    ϕ'  = p1 (p1 (p1 rw-b))
    ϕ'p = p2 (p1 (p1 rw-b))
    a   = p2 (p1 rw-b)
    b⇔ϕ'∧¬¬a = p1 (p2 rw-b)
    n≡∣ϕ'∣2¬ = p2 (p2 rw-b)

    ψ' = h ∨ (¬ (V a))

    -- remove all negations from ϕ'
    rm-ϕ' : Σ[ ((ϕ , ϕp) , (ψ , ψp)) ∈ (BE × HE2¬) ] ((ϕ' ⇒ ψ') ≡HT (ϕ ⇒ ψ))
    rm-ϕ' = remove-2¬-body ((ϕ' ⇒ ψ') , (ϕ'p , (hp , tt))) {n} {n≡∣ϕ'∣2¬}

    ϕ  = p1 (p1 (p1 rm-ϕ'))
    ϕp = p2 (p1 (p1 rm-ϕ'))
    ψ  = p1 (p2 (p1 rm-ϕ'))
    ψp = p2 (p2 (p1 rm-ϕ'))
    ϕ'⇒ψ'⇔ϕ⇒ψ = p2 rm-ϕ'

    proof =
      b ⇒ h                    ≡HT⟨ replace⇒lhs b⇔ϕ'∧¬¬a ⟩
      (ϕ' ∧ (¬ (¬ (V a)))) ⇒ h ≡HT⟨ rem2¬body ⟩
      ϕ' ⇒ (h ∨ (¬ (V a)))     ≡HT⟨def⟩
      ϕ' ⇒ ψ'                  ≡HT⟨ ϕ'⇒ψ'⇔ϕ⇒ψ ⟩
      ϕ ⇒ ψ                    ■

-- remove all double negation in a rule head -----------------------------------
-- every implication of a body expression b (without double negation) and
-- a head expression h with double negation can be rewritten as the
-- implication of a body expression ϕ (without double negation) and a
-- head expression ψ (without double negation)
-- b ⇒ h ⇔ ϕ ⇒ ψ
remove-2¬-head : ((b , _) : BE) → ((h , _) : HE2¬) → {n : ℕ} → {n ≡ ∣ h ∣2¬} →
                 Σ[ ((ϕ , _) , (ψ , _)) ∈ (BE × HE) ] ((b ⇒ h) ≡HT (ϕ ⇒ ψ))

remove-2¬-head (b , bp) (h , hp) {0} {0≡∣h∣2¬} =
  ((b , bp) , (h , HE2¬2HE (h , hp) 0≡∣h∣2¬)) , refl⇔

remove-2¬-head (b , bp) (h , hp) {suc n} {sn≡∣h∣2¬} =
  ((ϕ , ϕp) , (ψ , ψp)) , proof
  where
    -- rewrite h as ψ' ∨ ¬¬a
    rw-h : Σ[ ((ψ' , ψ'p) , a) ∈ (HE2¬ × Var) ]
           ((h ≡HT (ψ' ∨ (¬ (¬ (V a))))) × (n ≡ ∣ ψ' ∣2¬))
    rw-h = reorder-HE2¬ h hp {n} {sn≡∣h∣2¬}

    ψ'  = p1 (p1 (p1 rw-h))
    ψ'p = p2 (p1 (p1 rw-h))
    a   = p2 (p1 rw-h)
    h⇔ψ'∨¬¬a = p1 (p2 rw-h)
    n≡∣ψ'∣2¬ = p2 (p2 rw-h)

    ϕ' = b ∧ (¬ (V a))

    -- remove all negations from ψ'
    rm-ψ' : Σ[ ((ϕ , ϕp) , (ψ , ψp)) ∈ (BE × HE) ] ((ϕ' ⇒ ψ') ≡HT (ϕ ⇒ ψ))
    rm-ψ' = remove-2¬-head (ϕ' , (bp , tt)) (ψ' , ψ'p) {n} {n≡∣ψ'∣2¬}

    ϕ  = p1 (p1 (p1 rm-ψ'))
    ϕp = p2 (p1 (p1 rm-ψ'))
    ψ  = p1 (p2 (p1 rm-ψ'))
    ψp = p2 (p2 (p1 rm-ψ'))
    ϕ'⇒ψ'⇔ϕ⇒ψ = p2 rm-ψ'

    proof =
      b ⇒ h                    ≡HT⟨ replace⇒rhs h⇔ψ'∨¬¬a ⟩
      b ⇒ (ψ' ∨ (¬ (¬ (V a)))) ≡HT⟨ rem2¬head ⟩
      (b ∧ (¬ (V a))) ⇒ ψ'     ≡HT⟨def⟩
      ϕ' ⇒ ψ'                  ≡HT⟨ ϕ'⇒ψ'⇔ϕ⇒ψ ⟩
      ϕ ⇒ ψ                    ■

-- remove all double negation in a rule ----------------------------------------
-- every rule r with double negation can be rewritten as a rule ϕ
-- that does not contain double negation
r2¬-eq-r : ((r , _) : R2¬) → Σ[ (ϕ , _) ∈ R ] (r ≡HT ϕ)
r2¬-eq-r (r , rp) = ((ϕ ⇒ ψ) , (ϕp , ψp)) , proof
  where
    -- remove all negations from the body
    rm-b : Σ[ ((ϕ' , ϕ'p) , (ψ' , ψ'p)) ∈ (BE × HE2¬) ] (r ≡HT (ϕ' ⇒ ψ'))
    rm-b = remove-2¬-body (r , rp) {∣ (r , rp) ∣B2¬} {refl}

    ϕ'  = p1 (p1 (p1 rm-b))
    ϕ'p = p2 (p1 (p1 rm-b))
    ψ'  = p1 (p2 (p1 rm-b))
    ψ'p = p2 (p2 (p1 rm-b))
    r⇔ϕ'⇒ψ' = p2 rm-b

    -- remove all negations from the head
    rm-h : Σ[ ((ϕ , ϕp) , (ψ , ψp)) ∈ (BE × HE) ] ((ϕ' ⇒ ψ') ≡HT (ϕ ⇒ ψ))
    rm-h = remove-2¬-head (ϕ' , ϕ'p) (ψ' , ψ'p) {∣ ψ' ∣2¬} {refl}

    ϕ  = p1 (p1 (p1 rm-h))
    ϕp = p2 (p1 (p1 rm-h))
    ψ  = p1 (p2 (p1 rm-h))
    ψp = p2 (p2 (p1 rm-h))
    ϕ'⇒ψ'⇔ϕ⇒ψ = p2 rm-h

    proof =
         r    ≡HT⟨ r⇔ϕ'⇒ψ' ⟩
      ϕ' ⇒ ψ' ≡HT⟨ ϕ'⇒ψ'⇔ϕ⇒ψ ⟩
      ϕ  ⇒ ψ  ■

-- remove all double negation in a logic progam --------------------------------
-- every logic program lp with double negation can be rewritten as a
-- logic program Π that does not contain double negation
lp2¬-eq-lp : ((lp , _) : LP2¬) → Σ[ (Π , _) ∈ LP ] (Th2F lp ≡HT Th2F Π)
lp2¬-eq-lp (lp , lpp) = h lp lpp
  where
    -- same type as lp2¬-eq-lp but LP2¬ is split up into its parts
    -- this is necessary to avoid problems with the termination checker
    h : (lp : Th) → (isLP2¬ lp) → Σ[ (Π , _) ∈ LP ] (Th2F lp ≡HT Th2F Π)
    h [] tt = ([] , tt) , refl⇔
    h (r ∷ lp) (rp , lpp) = ((ϕ ∷ Π) , (ϕp , Πp)) , proof
      where
        -- remove all negations in the first rule
        rem-r : Σ[ (ϕ , ϕp) ∈ R ] (r ≡HT ϕ)
        rem-r = r2¬-eq-r (r , rp)

        ϕ  = p1 (p1 rem-r)
        ϕp = p2 (p1 rem-r)
        r⇔ϕ = p2 rem-r

        -- remove all negations in the rest of the logic program
        rem-lp : Σ[ (Π , Πp) ∈ LP ] (Th2F lp ≡HT Th2F Π)
        rem-lp = h lp lpp

        Π  = p1 (p1 rem-lp)
        Πp = p2 (p1 rem-lp)
        lp⇔Π = p2 rem-lp

        proof =
          Th2F (r ∷ lp) ≡HT⟨def⟩
          r ∧ Th2F lp   ≡HT⟨ replace∧lhs r⇔ϕ ⟩
          ϕ ∧ Th2F lp   ≡HT⟨ replace∧rhs lp⇔Π ⟩
          ϕ ∧ Th2F Π    ≡HT⟨def⟩
          Th2F (ϕ ∷ Π)  ■
