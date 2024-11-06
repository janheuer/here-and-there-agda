module HereAndThere.Tautologies where

open import Agda.Builtin.Sigma using (Σ) public
open import Agda.Builtin.Unit using (tt) renaming (⊤ to Unit) public

open import HereAndThere.Base
open import HereAndThere.Properties
open import HereAndThere.Equivalences
open import Formula.WithoutDisjunction

-- weak law of excluded middle -------------------------------------------------
-- ¬f ∨ ¬¬f
weak-lem : (f : F) → ValidHT ((¬ f) ∨ (¬ (¬ f)))
weak-lem f i@(IHT h t p) with lem {¬ f} t
... | inl t⊧C¬f  = inl (neg-c-to-ht t⊧C¬f)
... | inr t⊧C¬¬f = inr (neg-c-to-ht t⊧C¬¬f)

-- hosoi axiom -----------------------------------------------------------------
-- f ∨ (f ⇒ g) ∨ ¬g
hosoi : (f g : F) → ValidHT (f ∨ (f ⇒ g) ∨ (¬ g))
hosoi f g i@(IHT h t p) with 3val f i
... | inl i⊧HTf      = inl i⊧HTf
... | inr (inr t⊭Cf) = inr (inl ((λ i⊧HTf → Ø-elim (t⊭Cf (ht-to-c i⊧HTf))) ,
                                 (λ t⊧Cf → Ø-elim (t⊭Cf t⊧Cf))))
... | inr (inl (i⊭HTf , t⊧Cf)) with 3val g i
...   | inl i⊧HTg                = inr (inl ((λ _ → i⊧HTg) ,
                                             (λ _ → ht-to-c i⊧HTg)))
...   | inr (inl (i⊭HTg , t⊧Cg)) = inr (inl ((λ i⊧HTf → Ø-elim (i⊭HTf i⊧HTf)) ,
                                             (λ _ → t⊧Cg)))
...   | inr (inr t⊭Cg)           = inr (inr (neg-c-to-ht t⊭Cg))

-- removal of triple negation --------------------------------------------------
-- ¬¬¬f is equivalent to ¬f
reduce3¬ : {f : F} → (¬ (¬ (¬ f))) ≡HT (¬ f)
reduce3¬ {f} i@(IHT h t p) =
  let
    (proof⇒C , proof⇐C) = reduce2¬ {¬ f} t
    proof⇒HT = λ (_ , ⊧C¬¬f) → neg-c-to-ht (proof⇒C ⊧C¬¬f)
    proof⇐HT = λ (_ , ⊧C¬f)  → neg-c-to-ht (proof⇐C ⊧C¬f)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- currying --------------------------------------------------------------------
-- (f ∧ g) ⇒ j is equivalent to f ⇒ (g ⇒ j)
curry : {f g j : F} → ((f ∧ g) ⇒ j) ≡HT (f ⇒ (g ⇒ j))
curry {f} {g} {j} i@(IHT h t p) =
  let
    proof⇒C  rhs = λ ⊧f ⊧g → rhs (⊧f , ⊧g)
    proof⇒HT rhs = (λ ⊧f → ((λ ⊧g → (p1 rhs) (⊧f , ⊧g)) ,
                            (λ ⊧g → (p2 rhs) (ht-to-c ⊧f , ⊧g)))) ,
                   proof⇒C (p2 rhs)
    proof⇐C  lhs = λ (⊧f , ⊧g) → lhs ⊧f ⊧g
    proof⇐HT lhs = (λ (⊧f , ⊧g) → (p1 ((p1 lhs) ⊧f)) ⊧g) ,
                   proof⇐C (p2 lhs)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- combining two implications --------------------------------------------------
-- if f ⇒ g and f ⇒ j then f ⇒ (g ∧ j)
combine⇒ : {f g j : F} → ValidHT (f ⇒ g) → ValidHT (f ⇒ j) →
           ValidHT (f ⇒ (g ∧ j))
combine⇒ f⇒g f⇒j i@(IHT h t p) =
  let
    ⊧HTf⇒g , ⊧Cf⇒g = f⇒g i
    ⊧HTf⇒j , ⊧Cf⇒j = f⇒j i
    proofC  ⊧Cf  = ⊧Cf⇒g  ⊧Cf  , ⊧Cf⇒j  ⊧Cf
    proofHT ⊧HTf = ⊧HTf⇒g ⊧HTf , ⊧HTf⇒j ⊧HTf
  in
    proofHT , proofC

-- f ⇒ (g ⇒ j) is equivalent to g ⇒ (f ⇒ j) ------------------------------------
reorder⇒ : {f g j : F} → (f ⇒ (g ⇒ j)) ≡HT (g ⇒ (f ⇒ j))
reorder⇒ {f} {g} {j} i@(IHT h t p) =
  let
    proof⇒C  lhs = λ ⊧g ⊧f → lhs ⊧f ⊧g
    proof⇒HT lhs = (λ ⊧g → ((λ ⊧f → (p1 ((p1 lhs) ⊧f)) ⊧g) ,
                            proof⇒C (p2 lhs) (ht-to-c ⊧g))) ,
                   proof⇒C (p2 lhs)
    proof⇐C  rhs = λ ⊧f ⊧g → rhs ⊧g ⊧f
    proof⇐HT rhs = (λ ⊧f → ((λ ⊧g → (p1 ((p1 rhs) ⊧g)) ⊧f) ,
                            proof⇐C (p2 rhs) (ht-to-c ⊧f))) ,
                   proof⇐C (p2 rhs)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- de morgan ∧------------------------------------------------------------------
-- ¬(f ∧ g) is equivalent to ¬f ∨ ¬g
-- ¬(f ∧ g) implies ¬f ∨ ¬g
demorgan∧⇒ : (f g : F) → ValidHT ((¬ (f ∧ g)) ⇒ ((¬ f) ∨ (¬ g)))
demorgan∧⇒ f g i@(IHT h t p) with hosoi f g i
... | inl i⊧HTf =
  let
    proofC  = λ t⊭Cf∧g → inr (λ t⊧Cg → t⊭Cf∧g (ht-to-c i⊧HTf , t⊧Cg))
    proofHT = λ (i⊭HTf∧g , t⊭Cf∧g) → inr ((λ i⊧HTg → i⊭HTf∧g (i⊧HTf , i⊧HTg)) ,
                                          (λ t⊧Cg → t⊭Cf∧g (ht-to-c i⊧HTf ,
                                                            t⊧Cg)))
  in
    proofHT , proofC
... | inr (inl (i⊧HTf⇒g , t⊧Cf⇒g)) =
  let
    proofC  = λ t⊭Cf∧g → inl (λ t⊧Cf → t⊭Cf∧g (t⊧Cf , t⊧Cf⇒g t⊧Cf))
    proofHT = λ (i⊭HTf∧g , t⊭Cf∧g) → inl ((λ i⊧HTf → i⊭HTf∧g (i⊧HTf ,
                                                              i⊧HTf⇒g i⊧HTf)) ,
                                          (λ t⊧Cf → t⊭Cf∧g (t⊧Cf ,
                                                            t⊧Cf⇒g t⊧Cf)))
  in
    proofHT , proofC
... | inr (inr (i⊭HTg , t⊭Cg)) =
  let
    proofC  = λ _ → inr t⊭Cg
    proofHT = λ _ → inr (i⊭HTg , t⊭Cg)
  in
    proofHT , proofC

-- ¬f ∨ ¬g implies ¬(f ∧ g)
demorgan∧⇐ : (f g : F) → ValidHT (((¬ f) ∨ (¬ g)) ⇒ (¬ (f ∧ g)))
demorgan∧⇐ f g i@(IHT h t p) =
  let
    t⊧C¬f⇒¬[f∧g]  = λ t⊭Cf (t⊧Cf , _) → t⊭Cf t⊧Cf
    i⊧HT¬f⇒¬[f∧g] = λ (i⊭HTf , t⊭Cf)  → ((λ (i⊧HTf , _) → i⊭HTf i⊧HTf) ,
                                         t⊧C¬f⇒¬[f∧g] t⊭Cf)
    t⊧C¬g⇒¬[f∧g]  = λ t⊭Cg (_ , t⊧Cg) → t⊭Cg t⊧Cg
    i⊧HT¬g⇒¬[f∧g] = λ (i⊭HTg , t⊭Cg)  → ((λ (_ , i⊧HTg) → i⊭HTg i⊧HTg) ,
                                         t⊧C¬g⇒¬[f∧g] t⊭Cg)
  in
    ([ i⊧HT¬f⇒¬[f∧g] , i⊧HT¬g⇒¬[f∧g] ] , [ t⊧C¬f⇒¬[f∧g] , t⊧C¬g⇒¬[f∧g] ])

-- ¬(f ∧ g) is equivalent to ¬f ∨ ¬g
demorgan∧ : (f g : F) → (¬ (f ∧ g)) ≡HT ((¬ f) ∨ (¬ g))
demorgan∧ f g = ⇒⇐2⇔ (demorgan∧⇒ f g) (demorgan∧⇐ f g)

-- de morgan ∨ -----------------------------------------------------------------
-- ¬(f ∨ g) is equivalent to ¬f ∧ ¬g
-- ¬(f ∨ g) implies ¬f ∧ ¬g
demorgan∨⇒ : (f g : F) → ValidHT ((¬ (f ∨ g)) ⇒ ((¬ f) ∧ (¬ g)))
demorgan∨⇒ f g i@(IHT h t p) =
  let
    proofC  = λ ⊭f∨g → (λ ⊧f → ⊭f∨g (inl ⊧f)) ,
                       (λ ⊧g → ⊭f∨g (inr ⊧g))
    proofHT = λ (⊭HTf∨g , ⊭Cf∨g) → ((λ ⊧HTf → ⊭HTf∨g (inl ⊧HTf)) ,
                                    p1 (proofC ⊭Cf∨g)) ,
                                   ((λ ⊧HTg → ⊭HTf∨g (inr ⊧HTg)) ,
                                    p2 (proofC ⊭Cf∨g))
  in
    proofHT , proofC

demorgan∨⇐ : (f g : F) → ValidHT (((¬ f) ∧ (¬ g)) ⇒ (¬ (f ∨ g)))
demorgan∨⇐ f g i@(IHT h t p) =
  let
    proofC  = λ (⊭f , ⊭g)
                → λ { (inl ⊧f) → ⊭f ⊧f
                    ; (inr ⊧g) → ⊭g ⊧g }
    proofHT = λ ((⊭HTf , ⊭Cf) , (⊭HTg , ⊭Cg))
                → (λ { (inl ⊧HTf) → ⊭HTf ⊧HTf
                     ; (inr ⊧HTg) → ⊭HTg ⊧HTg }) ,
                  proofC (⊭Cf , ⊭Cg)
  in
    proofHT , proofC

demorgan∨ : (f g : F) → (¬ (f ∨ g)) ≡HT ((¬ f) ∧ (¬ g))
demorgan∨ f g = ⇒⇐2⇔ (demorgan∨⇒ f g) (demorgan∨⇐ f g)

-- disjunctions in ht can be rewritten with implication ------------------------
-- f ∨ g is equivalent to ((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)
-- f ∨ g implies ((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)
∨2⇒-⇒ : (f g : F) → ValidHT ((f ∨ g) ⇒ (((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)))
∨2⇒-⇒ f g i@(IHT h t p) =
  let
    t⊧Cf⇒rhs  = λ t⊧Cf → ((λ t⊧Cf⇒g → t⊧Cf⇒g t⊧Cf) , (λ _ → t⊧Cf))
    i⊧HTf⇒rhs = λ i⊧HTf → (((λ (i⊧HTf⇒g , _) → i⊧HTf⇒g i⊧HTf) ,
                            p1 (t⊧Cf⇒rhs (ht-to-c i⊧HTf))) ,
                           ((λ _ → i⊧HTf) ,
                            p2 (t⊧Cf⇒rhs (ht-to-c i⊧HTf))))
    t⊧Cg⇒rhs  = λ t⊧Cg → ((λ _ → t⊧Cg) , (λ t⊧Cg⇒f → t⊧Cg⇒f t⊧Cg))
    i⊧HTg⇒rhs = λ i⊧HTg → (((λ _ → i⊧HTg) ,
                            p1 (t⊧Cg⇒rhs (ht-to-c i⊧HTg))) ,
                           ((λ (i⊧HTg⇒f , _) → i⊧HTg⇒f i⊧HTg) ,
                            p2 (t⊧Cg⇒rhs (ht-to-c i⊧HTg))))
  in
    ([ i⊧HTf⇒rhs , i⊧HTg⇒rhs ] , [ t⊧Cf⇒rhs , t⊧Cg⇒rhs ])

-- ((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f) implies f ∨ g
∨2⇒-⇐ : (f g : F) → ValidHT ((((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)) ⇒ (f ∨ g))
∨2⇒-⇐  f g i@(IHT h t p) with hosoi f g i
... | inl i⊧HTf =
  let
    proofC  = λ _ → inl (ht-to-c i⊧HTf)
    proofHT = λ _ → inl i⊧HTf
  in
    proofHT , proofC
... | inr (inl i⊧HTf⇒g) =
  let
    proofC  = λ (t⊧C[f⇒g]⇒g  , _) → inr (t⊧C[f⇒g]⇒g (ht-to-c i⊧HTf⇒g))
    proofHT = λ (i⊧HT[f⇒g]⇒g , _) → inr ((p1 i⊧HT[f⇒g]⇒g) i⊧HTf⇒g)
  in
    proofHT , proofC
... | inr (inr i⊧HT¬g) =
  let
    proofC  = λ (_ , t⊧C[g⇒f]⇒f)
                → inl (t⊧C[g⇒f]⇒f (λ t⊧Cg → Ø-elim ((p2 i⊧HT¬g) t⊧Cg)))
    proofHT = λ (_ , i⊧HT[g⇒f]⇒f)
                → inl ((p1 i⊧HT[g⇒f]⇒f) ((λ i⊧HTg
                                            → Ø-elim ((p1 i⊧HT¬g) i⊧HTg)) ,
                                         (λ t⊧Cg → Ø-elim ((p2 i⊧HT¬g) t⊧Cg))))
  in
    proofHT , proofC

-- f ∨ g is equivalent to ((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)
∨2⇒ : (f g : F) → (f ∨ g) ≡HT (((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f))
∨2⇒ f g = ⇒⇐2⇔ (∨2⇒-⇒ f g) (∨2⇒-⇐ f g)

∨2⇒Σ : (f g : F) → Σ F (λ j → (f ∨ g) ≡HT j)
∨2⇒Σ f g = (((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)) , ∨2⇒ f g

-- every formula is equivalent to a formula that does not contain disjunction
F2F\∨ : (f : F) → Σ F\∨ (λ g → f ≡HT (f\∨f g))
F2F\∨ ⊥       = (f\∨ ⊥ tt) , refl⇔
F2F\∨ (V a)   = (f\∨ (V a) tt) , refl⇔
F2F\∨ (f ∧ g) =
  let
    (f\∨ f' f'p , f⇔f') = F2F\∨ f
    (f\∨ g' g'p , g⇔g') = F2F\∨ g
    f'∧g'isF\∨ = f'p , g'p
    f∧g⇔f'∧g' = f  ∧ g  ≡HT⟨ replace∧lhs f⇔f' ⟩
                f' ∧ g  ≡HT⟨ replace∧rhs g⇔g' ⟩
                f' ∧ g' ■
  in
    (f\∨ (f' ∧ g') f'∧g'isF\∨) , f∧g⇔f'∧g'
F2F\∨ (f ⇒ g) =
  let
    (f\∨ f' f'p , f⇔f') = F2F\∨ f
    (f\∨ g' g'p , g⇔g') = F2F\∨ g
    f'⇒g'isF\∨ = f'p , g'p
    f⇒g⇔f'⇒g' = f  ⇒ g  ≡HT⟨ replace⇒lhs f⇔f' ⟩
                f' ⇒ g  ≡HT⟨ replace⇒rhs g⇔g' ⟩
                f' ⇒ g' ■
  in
    (f\∨ (f' ⇒ g') f'⇒g'isF\∨) , f⇒g⇔f'⇒g'
F2F\∨ (f ∨ g) =
  let
    (f\∨ f' f'p , f⇔f') = F2F\∨ f
    (f\∨ g' g'p , g⇔g') = F2F\∨ g
    (ϕ , f'∨g'⇔ϕ) = ∨2⇒Σ f' g'
    ϕisF\∨ = ((f'p , g'p) , g'p) , ((g'p , f'p) , f'p)
    f∨g⇔ϕ = f  ∨ g  ≡HT⟨ replace∨lhs f⇔f' ⟩
            f' ∨ g  ≡HT⟨ replace∨rhs g⇔g' ⟩
            f' ∨ g' ≡HT⟨ f'∨g'⇔ϕ ⟩
            ϕ       ■
  in
    (f\∨ ϕ ϕisF\∨) , f∨g⇔ϕ

-- removal of nested implication -----------------------------------------------
-- (f ⇒ g) ⇒ k is equivalent to (g ∨ ¬f) ⇒ k and k ∨ f ∨ ¬g
-- (lemma 1)
-- (f ⇒ g) ⇒ k implies (g ∨ ¬f) ⇒ k
rem-nested⇒-⇒1 : (f g k : F) → ValidHT (((f ⇒ g) ⇒ k) ⇒ ((g ∨ (¬ f)) ⇒ k))
rem-nested⇒-⇒1 f g k i@(IHT h t p) =
  let
    proofC  lhs = [ (λ t⊧Cg → lhs (λ _ → t⊧Cg)) ,
                    (λ t⊭Cf → lhs (λ t⊧Cf → Ø-elim (t⊭Cf t⊧Cf))) ]
    proofHT lhs = [ (λ i⊧HTg
                       → (p1 lhs) ((λ _ → i⊧HTg) ,
                                   (λ _ → ht-to-c i⊧HTg))) ,
                    (λ i⊧HT¬f
                       → (p1 lhs) ((λ i⊧HTf → Ø-elim ((p1 i⊧HT¬f) i⊧HTf)) ,
                                   (λ t⊧Cf  → Ø-elim ((p2 i⊧HT¬f) t⊧Cf)))) ] ,
                  proofC (p2 lhs)
  in
    proofHT , proofC

-- (f ⇒ g) ⇒ k implies k ∨ f ∨ ¬g
rem-nested⇒-⇒2 : (f g k : F) → ValidHT (((f ⇒ g) ⇒ k) ⇒ (k ∨ f ∨ (¬ g)))
rem-nested⇒-⇒2 f g k i@(IHT h t p) with hosoi f g i
... | inl i⊧HTf =
  let
    proofC  = λ _ → inr (inl (ht-to-c i⊧HTf))
    proofHT = λ _ → inr (inl i⊧HTf)
  in
    proofHT , proofC
... | inr (inl i⊧HTf⇒g) =
  let
    proofC  = λ t⊧C[f⇒g]⇒k  → inl (t⊧C[f⇒g]⇒k (p2 i⊧HTf⇒g))
    proofHT = λ i⊧HT[f⇒g]⇒k → inl ((p1 i⊧HT[f⇒g]⇒k) i⊧HTf⇒g)
  in
    proofHT , proofC
... | inr (inr i⊧HT¬g) =
  let
    proofC  = λ _ → inr (inr (p2 i⊧HT¬g))
    proofHT = λ _ → inr (inr i⊧HT¬g)
  in
    proofHT , proofC

-- (f ⇒ g) ⇒ k implies (g ∨ ¬f) ⇒ k and k ∨ f ∨ ¬g
rem-nested⇒-⇒ : (f g k : F) →
                ValidHT (((f ⇒ g) ⇒ k) ⇒ (((g ∨ (¬ f)) ⇒ k) ∧ (k ∨ f ∨ (¬ g))))
rem-nested⇒-⇒ f g k = combine⇒ (rem-nested⇒-⇒1 f g k) (rem-nested⇒-⇒2 f g k)

-- (g ∨ ¬f) ⇒ k and k ∨ f ∨ ¬g implies (f ⇒ g) ⇒ k
rem-nested⇒-⇐ : (f g k : F) →
              ValidHT ((((g ∨ (¬ f)) ⇒ k) ∧ (k ∨ f ∨ (¬ g))) ⇒ ((f ⇒ g) ⇒ k))
rem-nested⇒-⇐ f g k i@(IHT h t p) =
  let
    proofC  = λ { (t⊧C[g∨¬f]⇒k , inl t⊧Ck)
                  → (λ _ → t⊧Ck)
                ; (t⊧C[g∨¬f]⇒k , inr (inl t⊧Cf))
                  → (λ t⊧Cf⇒g → t⊧C[g∨¬f]⇒k (inl (t⊧Cf⇒g t⊧Cf)))
                ; (t⊧C[g∨¬f]⇒k , inr (inr t⊧C¬g))
                  → (λ t⊧Cf⇒g → t⊧C[g∨¬f]⇒k (inr (λ t⊧Cf
                                                    → t⊧C¬g (t⊧Cf⇒g t⊧Cf)))) }
    proofHT = λ { (i⊧HT[g∨¬f]⇒k , inl i⊧HTk)
                  → ((λ _ → i⊧HTk) ,
                     (proofC (p2 i⊧HT[g∨¬f]⇒k ,
                              inl (ht-to-c i⊧HTk))))
                ; (i⊧HT[g∨¬f]⇒k , inr (inl i⊧HTf))
                  → ((λ (i⊧HTf⇒g , _)
                        → (p1 i⊧HT[g∨¬f]⇒k) (inl (i⊧HTf⇒g i⊧HTf))) ,
                     (proofC (p2 i⊧HT[g∨¬f]⇒k ,
                              inr (inl (ht-to-c i⊧HTf)))))
                ; (i⊧HT[g∨¬f]⇒k , inr (inr i⊧HT¬g))
                  → ((λ (i⊧HTf⇒g , t⊧Cf⇒g)
                        → (p1 i⊧HT[g∨¬f]⇒k)
                          (inr ((λ i⊧HTf → (p1 i⊧HT¬g) (i⊧HTf⇒g i⊧HTf)) ,
                                (λ t⊧Cf → (p2 i⊧HT¬g) (t⊧Cf⇒g t⊧Cf))))) ,
                     (proofC (p2 i⊧HT[g∨¬f]⇒k ,
                              inr (inr (p2 i⊧HT¬g))))) }
  in
    proofHT , proofC

-- (f ⇒ g) ⇒ k is equivalent to (g ∨ ¬f) ⇒ k and k ∨ f ∨ ¬g
rem-nested⇒ : (f g k : F) → ((f ⇒ g) ⇒ k) ≡HT
                            (((g ∨ (¬ f)) ⇒ k) ∧ (k ∨ f ∨ (¬ g)))
rem-nested⇒ f g k = ⇒⇐2⇔ (rem-nested⇒-⇒ f g k) (rem-nested⇒-⇐ f g k)

-- helper lemma for lemma 2
-- (f ⇒ g) ⇒ (j ⇒ k) is equivalent to ((j ∧ (g ∨ ¬f)) ⇒ k) ∧ (j ⇒ (k ∨ f ∨ ¬g))
f⇒f-eq-f∧f : (f g j k : F) →
             ((f ⇒ g) ⇒ (j ⇒ k)) ≡HT
             (((j ∧ (g ∨ (¬ f))) ⇒ k) ∧ (j ⇒ (k ∨ (f ∨ (¬ g)))))
f⇒f-eq-f∧f f g j k =
    (f ⇒ g) ⇒ (j ⇒ k)
  ≡HT⟨ reorder⇒ ⟩
    j ⇒ ((f ⇒ g) ⇒ k)
  ≡HT⟨ replace⇒rhs (rem-nested⇒ f g k) ⟩
    j ⇒ (((g ∨ (¬ f)) ⇒ k) ∧ (k ∨ f ∨ (¬ g)))
  ≡HT⟨ distr⇒∧ ⟩
    (j ⇒ ((g ∨ (¬ f)) ⇒ k)) ∧ (j ⇒ (k ∨ f ∨ (¬ g)))
  ≡HT⟨ replace∧lhs (symm⇔ curry) ⟩
    ((j ∧ (g ∨ (¬ f))) ⇒ k) ∧ (j ⇒ (k ∨ f ∨ (¬ g)))
  ■

f⇒f-eq-f∧fΣ : (f g j k : F) → Σ F (λ ϕ → ((f ⇒ g) ⇒ (j ⇒ k)) ≡HT ϕ)
f⇒f-eq-f∧fΣ f g j k =
  let
    ϕ = ((j ∧ (g ∨ (¬ f))) ⇒ k) ∧ (j ⇒ (k ∨ (f ∨ (¬ g))))
    proof = f⇒f-eq-f∧f f g j k
  in
    ϕ , proof

-- removal of double negation in implications ----------------------------------
-- removal of double negation in the body
-- (¬¬f ∧ g) ⇒ j is equivalent to g ⇒ (j ∨ ¬f)
rem2¬body : (f g j : F) → (((¬ (¬ f)) ∧ g) ⇒ j) ≡HT (g ⇒ (j ∨ (¬ f)))
rem2¬body f g j i@(IHT h t p) = (< proof⇒HT_HT , proof⇒HT_C > , proof⇒C) ,
                                (< proof⇐HT_HT , proof⇐HT_C > , proof⇐C)
  where
    proof⇒C : t ⊧C (((¬ (¬ f)) ∧ g) ⇒ j) → t ⊧C (g ⇒ (j ∨ (¬ f)))
    proof⇒C ⊧¬¬f∧g⇒j ⊧g with lem {¬ f} t
    ... | inl ⊧¬f = inr ⊧¬f
    ... | inr ⊧¬¬f = inl (⊧¬¬f∧g⇒j (⊧¬¬f , ⊧g))

    proof⇒HT_C : i ⊧HT (((¬ (¬ f)) ∧ g) ⇒ j) → t ⊧C g → t ⊧C (j ∨ (¬ f))
    proof⇒HT_C (_ , ⊧C¬¬f∧g⇒j) = proof⇒C ⊧C¬¬f∧g⇒j

    proof⇒HT_HT : i ⊧HT (((¬ (¬ f)) ∧ g) ⇒ j) → i ⊧HT g → i ⊧HT (j ∨ (¬ f))
    proof⇒HT_HT (⊧HT¬¬f∧g⇒j , _) ⊧HTg with weak-lem f i
    ... | inl ⊧HT¬f  = inr ⊧HT¬f
    ... | inr ⊧HT¬¬f = inl (⊧HT¬¬f∧g⇒j (⊧HT¬¬f , ⊧HTg))

    proof⇐C : t ⊧C (g ⇒ (j ∨ (¬ f))) → t ⊧C (((¬ (¬ f)) ∧ g) ⇒ j)
    proof⇐C ⊧g⇒j∨¬f (⊧¬¬f , ⊧g) with ⊧g⇒j∨¬f ⊧g
    ... | inl ⊧j  = ⊧j
    ... | inr ⊧¬f = Ø-elim (⊧¬¬f ⊧¬f)

    proof⇐HT_C : i ⊧HT (g ⇒ (j ∨ (¬ f))) → t ⊧C ((¬ (¬ f)) ∧ g) → t ⊧C j
    proof⇐HT_C (_ , ⊧Cg⇒j∨¬f) = proof⇐C ⊧Cg⇒j∨¬f

    proof⇐HT_HT : i ⊧HT (g ⇒ (j ∨ (¬ f))) → i ⊧HT ((¬ (¬ f)) ∧ g) → i ⊧HT j
    proof⇐HT_HT (⊧HTg⇒j∨¬f , _) (⊧HT¬¬f , ⊧HTg) with ⊧HTg⇒j∨¬f ⊧HTg
    ... | inl ⊧HTj  = ⊧HTj
    ... | inr ⊧HT¬f = Ø-elim ((p1 ⊧HT¬¬f) ⊧HT¬f)

-- removal of double negation in the head
-- f ⇒ (g ∨ ¬¬j) is equivalent to (f ∧ ¬j) ⇒ g
rem2¬head : (f g j : F) → (f ⇒ (g ∨ (¬ (¬ j)))) ≡HT ((f ∧ (¬ j)) ⇒ g)
rem2¬head f g j i@(IHT h t p) = (< proof⇒HT_HT , proof⇒HT_C > , proof⇒C) ,
                                (< proof⇐HT_HT , proof⇐HT_C > , proof⇐C)
  where
    proof⇒C : t ⊧C (f ⇒ (g ∨ (¬ (¬ j)))) → t ⊧C ((f ∧ (¬ j)) ⇒ g)
    proof⇒C ⊧f⇒g∨¬¬j (⊧f , ⊧¬j) with ⊧f⇒g∨¬¬j ⊧f
    ... | inl ⊧g   = ⊧g
    ... | inr ⊧¬¬j = Ø-elim (⊧¬¬j ⊧¬j)

    proof⇒HT_C : i ⊧HT (f ⇒ (g ∨ (¬ (¬ j)))) → t ⊧C (f ∧ (¬ j)) → t ⊧C g
    proof⇒HT_C (_ , ⊧Cf⇒g∨¬¬j) = proof⇒C ⊧Cf⇒g∨¬¬j

    proof⇒HT_HT : i ⊧HT (f ⇒ (g ∨ (¬ (¬ j)))) → i ⊧HT (f ∧ (¬ j)) → i ⊧HT g
    proof⇒HT_HT (⊧HTf⇒g∨¬¬j , _) (⊧HTf , ⊧HT¬j) with ⊧HTf⇒g∨¬¬j ⊧HTf
    ... | inl ⊧HTg   = ⊧HTg
    ... | inr ⊧HT¬¬j = Ø-elim ((p1 ⊧HT¬¬j) ⊧HT¬j)

    proof⇐C : t ⊧C ((f ∧ (¬ j)) ⇒ g) → t ⊧C (f ⇒ (g ∨ (¬ (¬ j))))
    proof⇐C ⊧f∧¬j⇒g ⊧f with lem {¬ j} t
    ... | inl ⊧¬j  = inl (⊧f∧¬j⇒g (⊧f , ⊧¬j))
    ... | inr ⊧¬¬j = inr ⊧¬¬j

    proof⇐HT_C : i ⊧HT ((f ∧ (¬ j)) ⇒ g) → t ⊧C f → t ⊧C (g ∨ (¬ (¬ j)))
    proof⇐HT_C (_ , ⊧Cf∧¬j⇒g) = proof⇐C ⊧Cf∧¬j⇒g

    proof⇐HT_HT : i ⊧HT ((f ∧ (¬ j)) ⇒ g) → i ⊧HT f → i ⊧HT (g ∨ (¬ (¬ j)))
    proof⇐HT_HT (⊧HTf∧¬j⇒g , _) ⊧HTf with weak-lem j i
    ... | inl ⊧HT¬j  = inl (⊧HTf∧¬j⇒g (⊧HTf , ⊧HT¬j))
    ... | inr ⊧HT¬¬j = inr ⊧HT¬¬j
