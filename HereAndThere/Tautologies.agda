module HereAndThere.Tautologies where

open import HereAndThere.Base
open import HereAndThere.Properties
open import HereAndThere.Equivalences
open import Formula.WithoutDisjunction

-- weak law of excluded middle -------------------------------------------------
-- ¬f ∨ ¬¬f
weak-lem : {f : F} → ValidHT ((¬ f) ∨ (¬ (¬ f)))
weak-lem {f} i@(IHT h t p) with lem {¬ f} t
... | inl t⊧C¬f  = inl (neg-c-to-ht t⊧C¬f)
... | inr t⊧C¬¬f = inr (neg-c-to-ht t⊧C¬¬f)

-- hosoi axiom -----------------------------------------------------------------
-- f ∨ (f ⇒ g) ∨ ¬g
hosoi : {f g : F} → ValidHT (f ∨ (f ⇒ g) ∨ (¬ g))
hosoi {f} {g} i@(IHT h t p) with 3val f i
... | inl ⊧HTf      = inl ⊧HTf
... | inr (inr ⊭Cf) = inr (inl (¬f2f⇒* (neg-c-to-ht ⊭Cf) g))
... | inr (inl (⊭HTf , ⊧Cf)) with 3val g i
...   | inl ⊧HTg                = inr (inl ((λ _ → ⊧HTg) ,
                                            (λ _ → ht-to-c ⊧HTg)))
...   | inr (inl (⊭HTg , ⊧Cg))  = inr (inl ((λ ⊧HTf → contraHT ⊭HTf ⊧HTf) ,
                                            (λ _    → ⊧Cg)))
...   | inr (inr ⊭Cg)           = inr (inr (neg-c-to-ht ⊭Cg))

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
curry {f} {g} {j} i@(IHT h t p) = (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)
  where
    proof⇒C : t ⊧C ((f ∧ g) ⇒ j) → t ⊧C (f ⇒ (g ⇒ j))
    proof⇒C ⊧f∧g⇒j ⊧f ⊧g = ⊧f∧g⇒j (⊧f , ⊧g)

    proof⇒HT : i ⊧HT ((f ∧ g) ⇒ j) → i ⊧HT (f ⇒ (g ⇒ j))
    proof⇒HT (⊧HTf∧g⇒j , ⊧Cf∧g⇒j) =
      (λ ⊧HTf → ((λ ⊧HTg → ⊧HTf∧g⇒j (⊧HTf , ⊧HTg)) ,
                 (λ ⊧Cg → ⊧Cf∧g⇒j (ht-to-c ⊧HTf , ⊧Cg)))) ,
      proof⇒C ⊧Cf∧g⇒j

    proof⇐C : t ⊧C (f ⇒ (g ⇒ j)) → t ⊧C ((f ∧ g) ⇒ j)
    proof⇐C ⊧f⇒g⇒j (⊧f , ⊧g) = ⊧f⇒g⇒j ⊧f ⊧g

    proof⇐HT : i ⊧HT (f ⇒ (g ⇒ j)) → i ⊧HT ((f ∧ g) ⇒ j)
    proof⇐HT (⊧HTf⇒g⇒j , ⊧Cf⇒g⇒j) =
      (λ (⊧f , ⊧g) → (p1 (⊧HTf⇒g⇒j ⊧f)) ⊧g) ,
      proof⇐C ⊧Cf⇒g⇒j

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
reorder⇒ {f} {g} {j} =
  f ⇒ (g ⇒ j) ≡HT⟨ curry ⟩ˢ
  (f ∧ g) ⇒ j ≡HT⟨ replace⇒lhs comm∧ ⟩
  (g ∧ f) ⇒ j ≡HT⟨ curry ⟩
  g ⇒ (f ⇒ j) ■

-- de morgan ∧------------------------------------------------------------------
-- ¬(f ∧ g) is equivalent to ¬f ∨ ¬g
-- ¬(f ∧ g) implies ¬f ∨ ¬g
demorgan∧⇒ : (f g : F) → ValidHT ((¬ (f ∧ g)) ⇒ ((¬ f) ∨ (¬ g)))
demorgan∧⇒ f g i@(IHT h t p) with hosoi {f} {g} i
... | inl ⊧HTf = proofHT , proofC
  where
    proofC : t ⊧C (¬ (f ∧ g)) → t ⊧C ((¬ f) ∨ (¬ g))
    proofC ⊭Cf∧g = inr (λ ⊧Cg → ⊭Cf∧g (ht-to-c ⊧HTf , ⊧Cg))

    proofHT : i ⊧HT (¬ (f ∧ g)) → i ⊧HT ((¬ f) ∨ (¬ g))
    proofHT (⊭HTf∧g , ⊭Cf∧g) =
      inr ((λ ⊧HTg → ⊭HTf∧g (⊧HTf         , ⊧HTg)) ,
           (λ ⊧Cg  → ⊭Cf∧g  (ht-to-c ⊧HTf , ⊧Cg)))

... | inr (inl (⊧HTf⇒g , ⊧Cf⇒g)) = proofHT , proofC
  where
    proofC : t ⊧C (¬ (f ∧ g)) → t ⊧C ((¬ f) ∨ (¬ g))
    proofC ⊭Cf∧g = inl (λ ⊧Cf → ⊭Cf∧g (⊧Cf , ⊧Cf⇒g ⊧Cf))

    proofHT : i ⊧HT (¬ (f ∧ g)) → i ⊧HT ((¬ f) ∨ (¬ g))
    proofHT (⊭HTf∧g , ⊭Cf∧g) =
      inl ((λ ⊧HTf → ⊭HTf∧g (⊧HTf , ⊧HTf⇒g ⊧HTf)) ,
           (λ ⊧Cf  → ⊭Cf∧g  (⊧Cf  , ⊧Cf⇒g  ⊧Cf)))

... | inr (inr (⊭HTg , ⊭Cg)) = proofHT , proofC
  where
    proofC : t ⊧C (¬ (f ∧ g)) → t ⊧C ((¬ f) ∨ (¬ g))
    proofC _ = inr ⊭Cg

    proofHT : i ⊧HT (¬ (f ∧ g)) → i ⊧HT ((¬ f) ∨ (¬ g))
    proofHT _ = inr (⊭HTg , ⊭Cg)

-- ¬f ∨ ¬g implies ¬(f ∧ g)
demorgan∧⇐ : (f g : F) → ValidHT (((¬ f) ∨ (¬ g)) ⇒ (¬ (f ∧ g)))
demorgan∧⇐ f g i@(IHT h t p) = ([ ⊧HT¬f⇒¬[f∧g] , ⊧HT¬g⇒¬[f∧g] ] ,
                                [ ⊧C¬f⇒¬[f∧g] , ⊧C¬g⇒¬[f∧g] ])
  where
    ⊧C¬f⇒¬[f∧g] : t ⊧C (¬ f) → t ⊧C (¬ (f ∧ g))
    ⊧C¬f⇒¬[f∧g] ⊭Cf (⊧Cf , _) = ⊭Cf ⊧Cf

    ⊧HT¬f⇒¬[f∧g] : i ⊧HT (¬ f) → i ⊧HT (¬ (f ∧ g))
    ⊧HT¬f⇒¬[f∧g] (⊭HTf , ⊭Cf) = (λ (⊧HTf , _) → ⊭HTf ⊧HTf) ,
                                ⊧C¬f⇒¬[f∧g] ⊭Cf

    ⊧C¬g⇒¬[f∧g] : t ⊧C (¬ g) → t ⊧C (¬ (f ∧ g))
    ⊧C¬g⇒¬[f∧g] ⊭Cg (_ , ⊧Cg) = ⊭Cg ⊧Cg

    ⊧HT¬g⇒¬[f∧g] : i ⊧HT (¬ g) → i ⊧HT (¬ (f ∧ g))
    ⊧HT¬g⇒¬[f∧g] (⊭HTg , ⊭Cg) = (λ (_ , ⊧HTg) → ⊭HTg ⊧HTg) ,
                                ⊧C¬g⇒¬[f∧g] ⊭Cg

-- ¬(f ∧ g) is equivalent to ¬f ∨ ¬g
demorgan∧ : {f g : F} → (¬ (f ∧ g)) ≡HT ((¬ f) ∨ (¬ g))
demorgan∧ {f} {g} = ⇒⇐2⇔ (demorgan∧⇒ f g) (demorgan∧⇐ f g)

-- de morgan ∨ -----------------------------------------------------------------
-- ¬(f ∨ g) is equivalent to ¬f ∧ ¬g
-- ¬(f ∨ g) implies ¬f ∧ ¬g
demorgan∨⇒ : (f g : F) → ValidHT ((¬ (f ∨ g)) ⇒ ((¬ f) ∧ (¬ g)))
demorgan∨⇒ f g i@(IHT h t p) = < ⊭HTf , ⊭HTg > , < ⊭Cf , ⊭Cg >
  where
    ⊭Cf : t ⊧C (¬ (f ∨ g)) → t ⊧C (¬ f)
    ⊭Cf ⊭f∨g ⊧f = ⊭f∨g (inl ⊧f)

    ⊭Cg : t ⊧C (¬ (f ∨ g)) → t ⊧C (¬ g)
    ⊭Cg ⊭f∨g ⊧g = ⊭f∨g (inr ⊧g)

    ⊭HTf : i ⊧HT (¬ (f ∨ g)) → i ⊧HT (¬ f)
    ⊭HTf (⊭HTf∨g , ⊭Cf∨g) = (λ ⊧HTf → ⊭HTf∨g (inl ⊧HTf)) ,
                            ⊭Cf ⊭Cf∨g

    ⊭HTg : i ⊧HT (¬ (f ∨ g)) → i ⊧HT (¬ g)
    ⊭HTg (⊭HTf∨g , ⊭Cf∨g) = (λ ⊧HTg → ⊭HTf∨g (inr ⊧HTg)) ,
                            ⊭Cg ⊭Cf∨g

demorgan∨⇐ : (f g : F) → ValidHT (((¬ f) ∧ (¬ g)) ⇒ (¬ (f ∨ g)))
demorgan∨⇐ f g i@(IHT h t p) = proofHT , proofC
  where
    proofC : t ⊧C ((¬ f) ∧ (¬ g)) → t ⊧C (¬ (f ∨ g))
    proofC (⊭f , ⊭g) (inl ⊧f) = ⊭f ⊧f
    proofC (⊭f , ⊭g) (inr ⊧g) = ⊭g ⊧g

    proofHT : i ⊧HT ((¬ f) ∧ (¬ g)) → i ⊧HT (¬ (f ∨ g))
    proofHT ((⊭HTf , ⊭Cf) , (⊭HTg , ⊭Cg)) =
      (λ { (inl ⊧HTf) → ⊭HTf ⊧HTf
         ; (inr ⊧HTg) → ⊭HTg ⊧HTg }) ,
      proofC (⊭Cf , ⊭Cg)

demorgan∨ : {f g : F} → (¬ (f ∨ g)) ≡HT ((¬ f) ∧ (¬ g))
demorgan∨ {f} {g} = ⇒⇐2⇔ (demorgan∨⇒ f g) (demorgan∨⇐ f g)

-- disjunctions in ht can be rewritten with implication ------------------------
-- f ∨ g is equivalent to ((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)
-- f ∨ g implies ((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)
∨2⇒-⇒ : (f g : F) → ValidHT ((f ∨ g) ⇒ (((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)))
∨2⇒-⇒ f g i@(IHT h t p) =
  let
    ⊧Cf⇒[f⇒g⇒g]  ⊧Cf  = λ ⊧Cf⇒g → ⊧Cf⇒g ⊧Cf
    ⊧HTf⇒[f⇒g⇒g] ⊧HTf = (λ (⊧HTf⇒g , _) → ⊧HTf⇒g ⊧HTf) ,
                        ⊧Cf⇒[f⇒g⇒g] (ht-to-c ⊧HTf)

    ⊧Cf⇒[g⇒f⇒f]  ⊧Cf  = λ _ → ⊧Cf
    ⊧HTf⇒[g⇒f⇒f] ⊧HTf = (λ _ → ⊧HTf) ,
                        ⊧Cf⇒[g⇒f⇒f] (ht-to-c ⊧HTf)

    ⊧Cf⇒rhs  = < ⊧Cf⇒[f⇒g⇒g]  , ⊧Cf⇒[g⇒f⇒f]  >
    ⊧HTf⇒rhs = < ⊧HTf⇒[f⇒g⇒g] , ⊧HTf⇒[g⇒f⇒f] >

    ⊧Cg⇒[f⇒g⇒g]  ⊧Cg  = λ _ → ⊧Cg
    ⊧HTg⇒[f⇒g⇒g] ⊧HTg = (λ _ → ⊧HTg) ,
                        ⊧Cg⇒[f⇒g⇒g] (ht-to-c ⊧HTg)

    ⊧Cg⇒[g⇒f⇒f]  ⊧Cg  = λ ⊧Cg⇒f → ⊧Cg⇒f ⊧Cg
    ⊧HTg⇒[g⇒f⇒f] ⊧HTg = (λ (⊧HTg⇒f , _) → ⊧HTg⇒f ⊧HTg) ,
                        ⊧Cg⇒[g⇒f⇒f] (ht-to-c ⊧HTg)

    ⊧Cg⇒rhs  = < ⊧Cg⇒[f⇒g⇒g]  , ⊧Cg⇒[g⇒f⇒f]  >
    ⊧HTg⇒rhs = < ⊧HTg⇒[f⇒g⇒g] , ⊧HTg⇒[g⇒f⇒f] >
  in
    ([ ⊧HTf⇒rhs , ⊧HTg⇒rhs ] , [ ⊧Cf⇒rhs , ⊧Cg⇒rhs ])

-- ((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f) implies f ∨ g
∨2⇒-⇐ : (f g : F) → ValidHT ((((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)) ⇒ (f ∨ g))
∨2⇒-⇐  f g i@(IHT h t p) with hosoi {f} {g} i
... | inl ⊧HTf = proofHT , proofC
  where
    proofC : t ⊧C (((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)) → t ⊧C (f ∨ g)
    proofC _ = inl (ht-to-c ⊧HTf)

    proofHT : i ⊧HT (((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)) → i ⊧HT (f ∨ g)
    proofHT _ = inl ⊧HTf

... | inr (inl ⊧HTf⇒g) = proofHT , proofC
  where
    proofC : t ⊧C (((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)) → t ⊧C (f ∨ g)
    proofC (⊧C[f⇒g]⇒g  , _) = inr (⊧C[f⇒g]⇒g (ht-to-c ⊧HTf⇒g))

    proofHT : i ⊧HT (((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)) → i ⊧HT (f ∨ g)
    proofHT ((⊧HT[f⇒g]⇒g , _) , _) = inr (⊧HT[f⇒g]⇒g ⊧HTf⇒g)

... | inr (inr (⊭HTg , ⊭Cg)) = proofHT , proofC
  where
    proofC : t ⊧C (((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)) → t ⊧C (f ∨ g)
    proofC (_ , ⊧C[g⇒f]⇒f) = inl (⊧C[g⇒f]⇒f (λ ⊧Cg → contraC ⊭Cg ⊧Cg))

    proofHT : i ⊧HT (((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)) → i ⊧HT (f ∨ g)
    proofHT (_ , (⊧HT[g⇒f]⇒f , _)) =
      inl (⊧HT[g⇒f]⇒f ((λ ⊧HTg → contraHT ⊭HTg ⊧HTg) ,
                       (λ ⊧Cg  → contraC  ⊭Cg  ⊧Cg)))

-- f ∨ g is equivalent to ((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)
∨2⇒ : {f g : F} → (f ∨ g) ≡HT (((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f))
∨2⇒ {f} {g} = ⇒⇐2⇔ (∨2⇒-⇒ f g) (∨2⇒-⇐ f g)

∨2⇒Σ : (f g : F) → Σ[ j ∈ F ] ((f ∨ g) ≡HT j)
∨2⇒Σ f g = (((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)) , ∨2⇒

-- every formula is equivalent to a formula that does not contain disjunction
F2F\∨ : (f : F) → Σ[ (g , _) ∈ F\∨ ] (f ≡HT g)
F2F\∨ ⊥       = (⊥ , tt) , refl⇔
F2F\∨ (V a)   = ((V a) , tt) , refl⇔

F2F\∨ (f ∧ g) =
  let
    ((f' , f'p) , f⇔f') = F2F\∨ f
    ((g' , g'p) , g⇔g') = F2F\∨ g
    f'∧g'isF\∨ = f'p , g'p
    f∧g⇔f'∧g' = f  ∧ g  ≡HT⟨ replace∧lhs f⇔f' ⟩
                f' ∧ g  ≡HT⟨ replace∧rhs g⇔g' ⟩
                f' ∧ g' ■
  in
    ((f' ∧ g') , f'∧g'isF\∨) , f∧g⇔f'∧g'

F2F\∨ (f ⇒ g) =
  let
    ((f' , f'p) , f⇔f') = F2F\∨ f
    ((g' , g'p) , g⇔g') = F2F\∨ g
    f'⇒g'isF\∨ = f'p , g'p
    f⇒g⇔f'⇒g' = f  ⇒ g  ≡HT⟨ replace⇒lhs f⇔f' ⟩
                f' ⇒ g  ≡HT⟨ replace⇒rhs g⇔g' ⟩
                f' ⇒ g' ■
  in
    ((f' ⇒ g') , f'⇒g'isF\∨) , f⇒g⇔f'⇒g'

F2F\∨ (f ∨ g) =
  let
    ((f' , f'p) , f⇔f') = F2F\∨ f
    ((g' , g'p) , g⇔g') = F2F\∨ g
    (ϕ , f'∨g'⇔ϕ) = ∨2⇒Σ f' g'
    ϕisF\∨ = ((f'p , g'p) , g'p) , ((g'p , f'p) , f'p)
    f∨g⇔ϕ = f  ∨ g  ≡HT⟨ replace∨lhs f⇔f' ⟩
            f' ∨ g  ≡HT⟨ replace∨rhs g⇔g' ⟩
            f' ∨ g' ≡HT⟨ f'∨g'⇔ϕ ⟩
            ϕ       ■
  in
    (ϕ , ϕisF\∨) , f∨g⇔ϕ

-- removal of nested implication -----------------------------------------------
-- (f ⇒ g) ⇒ k is equivalent to (g ∨ ¬f) ⇒ k and k ∨ f ∨ ¬g
-- (lemma 1)
-- (f ⇒ g) ⇒ k implies (g ∨ ¬f) ⇒ k
rem-nested⇒-⇒1 : (f g k : F) → ValidHT (((f ⇒ g) ⇒ k) ⇒ ((g ∨ (¬ f)) ⇒ k))
rem-nested⇒-⇒1 f g k i@(IHT h t p) = proofHT , proofC
  where
    ⊧Cg⇒k : t ⊧C ((f ⇒ g) ⇒ k) → t ⊧C g → t ⊧C k
    ⊧Cg⇒k lhs ⊧Cg = lhs (λ _ → ⊧Cg)

    ⊧C¬f⇒k : t ⊧C ((f ⇒ g) ⇒ k) → t ⊧C (¬ f) → t ⊧C k
    ⊧C¬f⇒k lhs ⊭Cf = lhs (λ ⊧Cf → contraC ⊭Cf ⊧Cf)

    proofC : t ⊧C ((f ⇒ g) ⇒ k) → t ⊧C ((g ∨ (¬ f)) ⇒ k)
    proofC lhs = [ ⊧Cg⇒k lhs , ⊧C¬f⇒k lhs ]

    ⊧HTg⇒k : i ⊧HT ((f ⇒ g) ⇒ k) → i ⊧HT g → i ⊧HT k
    ⊧HTg⇒k (lhsHT , _) ⊧HTg = lhsHT ((λ _ → ⊧HTg) ,
                                     (λ _ → ht-to-c ⊧HTg))

    ⊧HT¬f⇒k : i ⊧HT ((f ⇒ g) ⇒ k) → i ⊧HT (¬ f) → i ⊧HT k
    ⊧HT¬f⇒k (lhsHT , _) (⊭HTf , ⊭Cf) = lhsHT ((λ ⊧HTf → contraHT ⊭HTf ⊧HTf) ,
                                              (λ ⊧Cf  → contraC  ⊭Cf  ⊧Cf))

    proofHT : i ⊧HT ((f ⇒ g) ⇒ k) → i ⊧HT ((g ∨ (¬ f)) ⇒ k)
    proofHT lhs = [ ⊧HTg⇒k lhs , ⊧HT¬f⇒k lhs ] , proofC (p2 lhs)

-- (f ⇒ g) ⇒ k implies k ∨ f ∨ ¬g
rem-nested⇒-⇒2 : (f g k : F) → ValidHT (((f ⇒ g) ⇒ k) ⇒ (k ∨ f ∨ (¬ g)))
rem-nested⇒-⇒2 f g k i@(IHT h t p) with hosoi {f} {g} i
... | inl ⊧HTf =
  let
    proofC  _ = inr (inl (ht-to-c ⊧HTf))
    proofHT _ = inr (inl ⊧HTf)
  in
    proofHT , proofC

... | inr (inl ⊧HTf⇒g) =
  let
    proofC  ⊧C[f⇒g]⇒k  = inl (⊧C[f⇒g]⇒k (p2 ⊧HTf⇒g))
    proofHT ⊧HT[f⇒g]⇒k = inl ((p1 ⊧HT[f⇒g]⇒k) ⊧HTf⇒g)
  in
    proofHT , proofC

... | inr (inr ⊧HT¬g) =
  let
    proofC  _ = inr (inr (p2 ⊧HT¬g))
    proofHT _ = inr (inr ⊧HT¬g)
  in
    proofHT , proofC

-- (f ⇒ g) ⇒ k implies (g ∨ ¬f) ⇒ k and k ∨ f ∨ ¬g
rem-nested⇒-⇒ : (f g k : F) →
                ValidHT (((f ⇒ g) ⇒ k) ⇒ (((g ∨ (¬ f)) ⇒ k) ∧ (k ∨ f ∨ (¬ g))))
rem-nested⇒-⇒ f g k = combine⇒ (rem-nested⇒-⇒1 f g k) (rem-nested⇒-⇒2 f g k)

-- (g ∨ ¬f) ⇒ k and k ∨ f ∨ ¬g implies (f ⇒ g) ⇒ k
rem-nested⇒-⇐ : (f g k : F) →
              ValidHT ((((g ∨ (¬ f)) ⇒ k) ∧ (k ∨ f ∨ (¬ g))) ⇒ ((f ⇒ g) ⇒ k))
rem-nested⇒-⇐ f g k i@(IHT h t p) = proofHT , proofC
  where
    proofC : t ⊧C (((g ∨ (¬ f)) ⇒ k) ∧ (k ∨ f ∨ (¬ g))) → t ⊧C ((f ⇒ g) ⇒ k)
    proofC (_ , (inl ⊧k)) _ =
      ⊧k

    proofC (⊧[g∨¬f]⇒k , (inr (inl ⊧f))) ⊧f⇒g =
      ⊧[g∨¬f]⇒k (inl (⊧f⇒g ⊧f))

    proofC (⊧[g∨¬f]⇒k , (inr (inr ⊧¬g))) ⊧f⇒g =
      ⊧[g∨¬f]⇒k (inr (λ ⊧f → ⊧¬g (⊧f⇒g ⊧f)))

    proofHT : i ⊧HT (((g ∨ (¬ f)) ⇒ k) ∧ (k ∨ f ∨ (¬ g))) → i ⊧HT ((f ⇒ g) ⇒ k)
    proofHT ((_ , ⊧C[g∨¬f]⇒k) , inl ⊧HTk) =
      (λ _ → ⊧HTk) ,
      proofC (⊧C[g∨¬f]⇒k , inl (ht-to-c ⊧HTk))

    proofHT ((⊧HT[g∨¬f]⇒k , ⊧C[g∨¬f]⇒k) , inr (inl ⊧HTf)) =
      (λ (⊧HTf⇒g , _) → ⊧HT[g∨¬f]⇒k (inl (⊧HTf⇒g ⊧HTf))) ,
      proofC (⊧C[g∨¬f]⇒k , inr (inl (ht-to-c ⊧HTf)))

    proofHT ((⊧HT[g∨¬f]⇒k , ⊧C[g∨¬f]⇒k) , inr (inr (⊭HTg , ⊭Cg))) =
      (λ (⊧HTf⇒g , ⊧Cf⇒g)
         → ⊧HT[g∨¬f]⇒k (inr ((λ ⊧HTf → ⊭HTg (⊧HTf⇒g ⊧HTf)) ,
                             (λ ⊧Cf  → ⊭Cg  (⊧Cf⇒g  ⊧Cf))))) ,
      proofC (⊧C[g∨¬f]⇒k , inr (inr ⊭Cg))

-- (f ⇒ g) ⇒ k is equivalent to (g ∨ ¬f) ⇒ k and k ∨ f ∨ ¬g
rem-nested⇒ : {f g k : F} → ((f ⇒ g) ⇒ k) ≡HT
                            (((g ∨ (¬ f)) ⇒ k) ∧ (k ∨ f ∨ (¬ g)))
rem-nested⇒ {f} {g} {k} = ⇒⇐2⇔ (rem-nested⇒-⇒ f g k) (rem-nested⇒-⇐ f g k)

-- helper lemma for lemma 2
-- (f ⇒ g) ⇒ (j ⇒ k) is equivalent to ((j ∧ (g ∨ ¬f)) ⇒ k) ∧ (j ⇒ (k ∨ f ∨ ¬g))
f⇒f-eq-f∧f : {f g j k : F} →
             ((f ⇒ g) ⇒ (j ⇒ k)) ≡HT
             (((j ∧ (g ∨ (¬ f))) ⇒ k) ∧ (j ⇒ (k ∨ (f ∨ (¬ g)))))
f⇒f-eq-f∧f {f} {g} {j} {k} =
    (f ⇒ g) ⇒ (j ⇒ k)
  ≡HT⟨ reorder⇒ ⟩
    j ⇒ ((f ⇒ g) ⇒ k)
  ≡HT⟨ replace⇒rhs rem-nested⇒ ⟩
    j ⇒ (((g ∨ (¬ f)) ⇒ k) ∧ (k ∨ f ∨ (¬ g)))
  ≡HT⟨ distr⇒∧ ⟩
    (j ⇒ ((g ∨ (¬ f)) ⇒ k)) ∧ (j ⇒ (k ∨ f ∨ (¬ g)))
  ≡HT⟨ replace∧lhs (symm⇔ curry) ⟩
    ((j ∧ (g ∨ (¬ f))) ⇒ k) ∧ (j ⇒ (k ∨ f ∨ (¬ g)))
  ■

f⇒f-eq-f∧fΣ : (f g j k : F) → Σ[ ϕ ∈ F ] (((f ⇒ g) ⇒ (j ⇒ k)) ≡HT ϕ)
f⇒f-eq-f∧fΣ f g j k = ((j ∧ (g ∨ (¬ f))) ⇒ k) ∧ (j ⇒ (k ∨ (f ∨ (¬ g)))) ,
                      f⇒f-eq-f∧f

-- removal of double negation in implications ----------------------------------
-- removal of double negation in the body
-- (¬¬f ∧ g) ⇒ j is equivalent to g ⇒ (j ∨ ¬f)
rem2¬body : {f g j : F} → (((¬ (¬ f)) ∧ g) ⇒ j) ≡HT (g ⇒ (j ∨ (¬ f)))
rem2¬body {f} {g} {j} i@(IHT h t p) = (< proof⇒HT_HT , proof⇒HT_C > , proof⇒C) ,
                                      (< proof⇐HT_HT , proof⇐HT_C > , proof⇐C)
  where
    proof⇒C : t ⊧C (((¬ (¬ f)) ∧ g) ⇒ j) → t ⊧C (g ⇒ (j ∨ (¬ f)))
    proof⇒C ⊧¬¬f∧g⇒j ⊧g with lem {¬ f} t
    ... | inl ⊧¬f = inr ⊧¬f
    ... | inr ⊧¬¬f = inl (⊧¬¬f∧g⇒j (⊧¬¬f , ⊧g))

    proof⇒HT_C : i ⊧HT (((¬ (¬ f)) ∧ g) ⇒ j) → t ⊧C g → t ⊧C (j ∨ (¬ f))
    proof⇒HT_C (_ , ⊧C¬¬f∧g⇒j) = proof⇒C ⊧C¬¬f∧g⇒j

    proof⇒HT_HT : i ⊧HT (((¬ (¬ f)) ∧ g) ⇒ j) → i ⊧HT g → i ⊧HT (j ∨ (¬ f))
    proof⇒HT_HT (⊧HT¬¬f∧g⇒j , _) ⊧HTg with weak-lem {f} i
    ... | inl ⊧HT¬f  = inr ⊧HT¬f
    ... | inr ⊧HT¬¬f = inl (⊧HT¬¬f∧g⇒j (⊧HT¬¬f , ⊧HTg))

    proof⇐C : t ⊧C (g ⇒ (j ∨ (¬ f))) → t ⊧C (((¬ (¬ f)) ∧ g) ⇒ j)
    proof⇐C ⊧g⇒j∨¬f (⊧¬¬f , ⊧g) with ⊧g⇒j∨¬f ⊧g
    ... | inl ⊧j  = ⊧j
    ... | inr ⊧¬f = contraC ⊧¬¬f ⊧¬f

    proof⇐HT_C : i ⊧HT (g ⇒ (j ∨ (¬ f))) → t ⊧C ((¬ (¬ f)) ∧ g) → t ⊧C j
    proof⇐HT_C (_ , ⊧Cg⇒j∨¬f) = proof⇐C ⊧Cg⇒j∨¬f

    proof⇐HT_HT : i ⊧HT (g ⇒ (j ∨ (¬ f))) → i ⊧HT ((¬ (¬ f)) ∧ g) → i ⊧HT j
    proof⇐HT_HT (⊧HTg⇒j∨¬f , _) (⊧HT¬¬f , ⊧HTg) with ⊧HTg⇒j∨¬f ⊧HTg
    ... | inl ⊧HTj  = ⊧HTj
    ... | inr ⊧HT¬f = contraHT {f = (¬ f)} (p1 ⊧HT¬¬f) ⊧HT¬f

-- removal of double negation in the head
-- f ⇒ (g ∨ ¬¬j) is equivalent to (f ∧ ¬j) ⇒ g
rem2¬head : {f g j : F} → (f ⇒ (g ∨ (¬ (¬ j)))) ≡HT ((f ∧ (¬ j)) ⇒ g)
rem2¬head {f} {g} {j} i@(IHT h t p) = (< proof⇒HT_HT , proof⇒HT_C > , proof⇒C) ,
                                      (< proof⇐HT_HT , proof⇐HT_C > , proof⇐C)
  where
    proof⇒C : t ⊧C (f ⇒ (g ∨ (¬ (¬ j)))) → t ⊧C ((f ∧ (¬ j)) ⇒ g)
    proof⇒C ⊧f⇒g∨¬¬j (⊧f , ⊧¬j) with ⊧f⇒g∨¬¬j ⊧f
    ... | inl ⊧g   = ⊧g
    ... | inr ⊧¬¬j = contraC {f = (¬ j)} ⊧¬¬j ⊧¬j

    proof⇒HT_C : i ⊧HT (f ⇒ (g ∨ (¬ (¬ j)))) → t ⊧C (f ∧ (¬ j)) → t ⊧C g
    proof⇒HT_C (_ , ⊧Cf⇒g∨¬¬j) = proof⇒C ⊧Cf⇒g∨¬¬j

    proof⇒HT_HT : i ⊧HT (f ⇒ (g ∨ (¬ (¬ j)))) → i ⊧HT (f ∧ (¬ j)) → i ⊧HT g
    proof⇒HT_HT (⊧HTf⇒g∨¬¬j , _) (⊧HTf , ⊧HT¬j) with ⊧HTf⇒g∨¬¬j ⊧HTf
    ... | inl ⊧HTg   = ⊧HTg
    ... | inr ⊧HT¬¬j = contraHT {f = (¬ j)} (p1 ⊧HT¬¬j) ⊧HT¬j

    proof⇐C : t ⊧C ((f ∧ (¬ j)) ⇒ g) → t ⊧C (f ⇒ (g ∨ (¬ (¬ j))))
    proof⇐C ⊧f∧¬j⇒g ⊧f with lem {¬ j} t
    ... | inl ⊧¬j  = inl (⊧f∧¬j⇒g (⊧f , ⊧¬j))
    ... | inr ⊧¬¬j = inr ⊧¬¬j

    proof⇐HT_C : i ⊧HT ((f ∧ (¬ j)) ⇒ g) → t ⊧C f → t ⊧C (g ∨ (¬ (¬ j)))
    proof⇐HT_C (_ , ⊧Cf∧¬j⇒g) = proof⇐C ⊧Cf∧¬j⇒g

    proof⇐HT_HT : i ⊧HT ((f ∧ (¬ j)) ⇒ g) → i ⊧HT f → i ⊧HT (g ∨ (¬ (¬ j)))
    proof⇐HT_HT (⊧HTf∧¬j⇒g , _) ⊧HTf with weak-lem {j} i
    ... | inl ⊧HT¬j  = inl (⊧HTf∧¬j⇒g (⊧HTf , ⊧HT¬j))
    ... | inr ⊧HT¬¬j = inr ⊧HT¬¬j
