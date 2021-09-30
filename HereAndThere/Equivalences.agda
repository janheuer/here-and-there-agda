module HereAndThere.Equivalences where

open import HereAndThere.Base
open import HereAndThere.Properties

-- some proofs on equivalences -------------------------------------------------
-- if f ⇒ g and g ⇒ f then f ⇔ g
⇒⇐2⇔ : {f g : F} → ValidHT (f ⇒ g) → ValidHT (g ⇒ f) → ValidHT (f ⇔ g)
⇒⇐2⇔ ⊧f⇒g ⊧g⇒f i = ⊧f⇒g i , ⊧g⇒f i

refl⇔ : (f : F) → ValidHT (f ⇔ f)
refl⇔ f i@(IHT h t p) =
  let
    proof⇒C  ⊧f = ⊧f
    proof⇒HT ⊧f = ⊧f
  in
    (proof⇒HT , proof⇒C) , (proof⇒HT , proof⇒C)

symm⇔ : {f g : F} → ValidHT (f ⇔ g) → ValidHT (g ⇔ f)
symm⇔ f⇔g i@(IHT h t p) =
  let
    ⊧f⇒g , ⊧g⇒f = f⇔g i
  in
    ⊧g⇒f , ⊧f⇒g

-- if f ⇔ g and g ⇔ j then f ⇔ j
trans⇔ : {f g j : F} → ValidHT (f ⇔ g) → ValidHT (g ⇔ j) → ValidHT (f ⇔ j)
trans⇔ ⊧f⇔g ⊧g⇔j i@(IHT h t p) =
  let
    ⊧f⇒g , ⊧g⇒f = ⊧f⇔g i
    ⊧g⇒j , ⊧j⇒g = ⊧g⇔j i
    proof⇒C  ⊧f = (p2 ⊧g⇒j) ((p2 ⊧f⇒g) ⊧f)
    proof⇒HT ⊧f = (p1 ⊧g⇒j) ((p1 ⊧f⇒g) ⊧f)
    proof⇐C  ⊧j = (p2 ⊧g⇒f) ((p2 ⊧j⇒g) ⊧j)
    proof⇐HT ⊧j = (p1 ⊧g⇒f) ((p1 ⊧j⇒g) ⊧j)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- if f ⇔ g then forall j: (j ⇒ f) ⇔ (j ⇒ g)
replace⇒rhs : {f g : F} → ValidHT (f ⇔ g) → (j : F) →
              ValidHT ((j ⇒ f) ⇔ (j ⇒ g))
replace⇒rhs ⊧f⇔g j i@(IHT h t p) =
  let
    ⊧f⇒g , ⊧g⇒f = ⊧f⇔g i
    proof⇒C  lhs = λ ⊧j → (p2 ⊧f⇒g) (lhs ⊧j)
    proof⇒HT lhs = ((λ ⊧j → (p1 ⊧f⇒g) ((p1 lhs) ⊧j)) ,
                    proof⇒C (p2 lhs))
    proof⇐C  rhs = λ ⊧j → (p2 ⊧g⇒f) (rhs ⊧j)
    proof⇐HT rhs = ((λ ⊧j → (p1 ⊧g⇒f) ((p1 rhs) ⊧j)) ,
                    proof⇐C (p2 rhs))
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- if f ⇔ g then forall j: (f ⇒ j) ⇔ (g ⇒ j)
replace⇒lhs : {f g : F} → ValidHT (f ⇔ g) → (j : F) →
              ValidHT ((f ⇒ j) ⇔ (g ⇒ j))
replace⇒lhs ⊧f⇔g j i@(IHT h t p) =
  let
    ⊧f⇒g , ⊧g⇒f = ⊧f⇔g i
    proof⇒C  lhs = λ ⊧g → lhs ((p2 ⊧g⇒f) ⊧g)
    proof⇒HT lhs = (λ ⊧g → (p1 lhs) ((p1 ⊧g⇒f) ⊧g)) ,
                   proof⇒C (p2 lhs)
    proof⇐C  rhs = λ ⊧f → rhs ((p2 ⊧f⇒g) ⊧f)
    proof⇐HT rhs = (λ ⊧f → (p1 rhs) ((p1 ⊧f⇒g) ⊧f)) ,
                   proof⇐C (p2 rhs)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

⊤-lid-⇒ : (f : F) → ValidHT ((⊤ ⇒ f) ⇔ f)
⊤-lid-⇒ f i@(IHT h t p) =
  let
    proof⇒C  ⊧⊤⇒f = ⊧⊤⇒f (λ ())
    proof⇒HT ⊧⊤⇒f = (p1 ⊧⊤⇒f) ((λ ()) , (λ ()))
    proof⇐C  ⊧f   = λ _ → ⊧f
    proof⇐HT ⊧f   = (λ _ → ⊧f) , proof⇐C (ht-to-c ⊧f)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- f ∧ g is equivalent to g ∧ f
symm∧ : (f g : F) → ValidHT ((f ∧ g) ⇔ (g ∧ f))
symm∧ f g i@(IHT h t p) =
  let
    proof⇒C  ⊧f∧g = (p2 ⊧f∧g) , (p1 ⊧f∧g)
    proof⇒HT ⊧f∧g = (p2 ⊧f∧g) , (p1 ⊧f∧g)
    proof⇐C  ⊧g∧f = (p2 ⊧g∧f) , (p1 ⊧g∧f)
    proof⇐HT ⊧g∧f = (p2 ⊧g∧f) , (p1 ⊧g∧f)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

assoc∧ : (f g j : F) → ValidHT (((f ∧ g) ∧ j) ⇔ (f ∧ (g ∧ j)))
assoc∧ f g j i@(IHT h t p) =
  let
    proof⇒C  = λ ((⊧f , ⊧g) , ⊧j) → (⊧f , (⊧g , ⊧j))
    proof⇒HT = λ ((⊧f , ⊧g) , ⊧j) → (⊧f , (⊧g , ⊧j))
    proof⇐C  = λ (⊧f , (⊧g , ⊧j)) → ((⊧f , ⊧g) , ⊧j)
    proof⇐HT = λ (⊧f , (⊧g , ⊧j)) → ((⊧f , ⊧g) , ⊧j)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- if f ⇔ g then forall j: (f ∧ j) ⇔ (g ∧ j)
replace∧lhs : {f g : F} → ValidHT (f ⇔ g) → (j : F) →
              ValidHT ((f ∧ j) ⇔ (g ∧ j))
replace∧lhs ⊧f⇔g j i@(IHT h t p) =
  let
    ⊧f⇒g , ⊧g⇒f = ⊧f⇔g i
    proof⇒C  = λ (⊧f , ⊧j) → (p2 ⊧f⇒g) ⊧f , ⊧j
    proof⇒HT = λ (⊧f , ⊧j) → (p1 ⊧f⇒g) ⊧f , ⊧j
    proof⇐C  = λ (⊧g , ⊧j) → (p2 ⊧g⇒f) ⊧g , ⊧j
    proof⇐HT = λ (⊧g , ⊧j) → (p1 ⊧g⇒f) ⊧g , ⊧j
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- if f ⇔ g then forall j: (j ∧ f) ⇔ (j ∧ g)
replace∧rhs : {f g : F} → ValidHT (f ⇔ g) → (j : F) →
              ValidHT ((j ∧ f) ⇔ (j ∧ g))
replace∧rhs {f} {g} f⇔g j =
  let
    j∧f⇔f∧j = symm∧ j f
    f∧j⇔g∧j = replace∧lhs f⇔g j
    g∧j⇔j∧g = symm∧ g j
  in
    trans⇔ (trans⇔ j∧f⇔f∧j f∧j⇔g∧j) g∧j⇔j∧g

-- f is equivalent to f ∧ ⊤
⊤-rid-∧ : (f : F) → ValidHT ((f ∧ ⊤) ⇔ f)
⊤-rid-∧ f i@(IHT h t p) =
  let
    proof⇒C  ⊧f∧⊤ = p1 ⊧f∧⊤
    proof⇒HT ⊧f∧⊤ = p1 ⊧f∧⊤
    proof⇐C  ⊧f   = ⊧f , (λ ())
    proof⇐HT ⊧f   = ⊧f , ((λ ()) , (λ ()))
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- f is equivalent to ⊤ ∧ f
⊤-lid-∧ : (f : F) → ValidHT ((⊤ ∧ f) ⇔ f)
⊤-lid-∧ f = trans⇔ (symm∧ ⊤ f) (⊤-rid-∧ f)

-- f ∨ g is equivalent to g ∨ f
symm∨ : (f g : F) → ValidHT ((f ∨ g) ⇔ (g ∨ f))
symm∨ f g i@(IHT h t p) =
  let
    proof⇒C  = λ { (inl ⊧f) → inr ⊧f
                 ; (inr ⊧g) → inl ⊧g }
    proof⇒HT = λ { (inl ⊧f) → inr ⊧f
                 ; (inr ⊧g) → inl ⊧g }
    proof⇐C  = λ { (inl ⊧g) → inr ⊧g
                 ; (inr ⊧f) → inl ⊧f }
    proof⇐HT = λ { (inl ⊧g) → inr ⊧g
                 ; (inr ⊧f) → inl ⊧f }
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- if f ⇔ g then forall j: (f ∨ j) ⇔ (g ∨ j)
replace∨lhs : {f g : F} → ValidHT (f ⇔ g) → (j : F) →
              ValidHT ((f ∨ j) ⇔ (g ∨ j))
replace∨lhs ⊧f⇔g j i@(IHT h t p) =
  let
    (⊧HTf⇒g , ⊧Cf⇒g) , (⊧HTg⇒f , ⊧Cg⇒f) = ⊧f⇔g i
    proof⇒C  = λ { (inl ⊧f) → inl (⊧Cf⇒g ⊧f)
                 ; (inr ⊧j) → inr ⊧j }
    proof⇒HT = λ { (inl ⊧f) → inl (⊧HTf⇒g ⊧f)
                 ; (inr ⊧j) → inr ⊧j }
    proof⇐C  = λ { (inl ⊧g) → inl (⊧Cg⇒f ⊧g)
                 ; (inr ⊧j) → inr ⊧j }
    proof⇐HT = λ { (inl ⊧g) → inl (⊧HTg⇒f ⊧g)
                 ; (inr ⊧j) → inr ⊧j }
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- if f ⇔ g then forall j: (j ∨ f) ⇔ (j ∨ g)
replace∨rhs : {f g : F} → ValidHT (f ⇔ g) → (j : F) →
              ValidHT ((j ∨ f) ⇔ (j ∨ g))
replace∨rhs {f} {g} f⇔g j =
  let
    j∨f⇔f∨j = symm∨ j f
    f∨j⇔g∨j = replace∨lhs f⇔g j
    g∨j⇔j∨g = symm∨ g j
  in
    trans⇔ (trans⇔ j∨f⇔f∨j f∨j⇔g∨j) g∨j⇔j∨g

-- some equivalence proofs -----------------------------------------------------
-- f ⇒ (g ⇒ j) is equivalent to g ⇒ (f ⇒ j)
reorder⇒ : (f g j : F) → ValidHT ((f ⇒ (g ⇒ j)) ⇔ (g ⇒ (f ⇒ j)))
reorder⇒ f g j i@(IHT h t p) =
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

-- f ⇒ (g ∧ j) is equivalent to (f ⇒ g) ∧ (f ⇒ j)
factor⇒∧ : (f g j : F) → ValidHT ((f ⇒ (g ∧ j)) ⇔ ((f ⇒ g) ∧ (f ⇒ j)))
factor⇒∧ f g j i@(IHT h t p) =
  let
    proof⇒C  lhs = (λ ⊧f → p1 (lhs ⊧f)) ,
                   (λ ⊧f → p2 (lhs ⊧f))
    proof⇒HT lhs = ((λ ⊧f → p1 ((p1 lhs) ⊧f)) ,
                    (λ ⊧f → (p1 (proof⇒C (p2 lhs))) ⊧f)) ,
                   ((λ ⊧f → p2 ((p1 lhs) ⊧f)) ,
                    (λ ⊧f → (p2 (proof⇒C (p2 lhs))) ⊧f))
    proof⇐C  rhs = λ ⊧f → ((p1 rhs) ⊧f ,
                           (p2 rhs) ⊧f)
    proof⇐HT rhs = (λ ⊧f → ((p1 (p1 rhs)) ⊧f ,
                            (p1 (p2 rhs)) ⊧f)) ,
                   (λ ⊧f → proof⇐C (p2 (p1 rhs) , p2 (p2 rhs)) ⊧f)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- f ⇒ (g ⇒ j) is equivalent to (f ∧ g) ⇒ j
uncurry : (f g j : F) → ValidHT ((f ⇒ (g ⇒ j)) ⇔ ((f ∧ g) ⇒ j))
uncurry f g j i@(IHT h t p) =
  let
    proof⇒C  lhs = λ (⊧f , ⊧g) → lhs ⊧f ⊧g
    proof⇒HT lhs = (λ (⊧f , ⊧g) → (p1 ((p1 lhs) ⊧f)) ⊧g) ,
                   proof⇒C (p2 lhs)
    proof⇐C  rhs = λ ⊧f ⊧g → rhs (⊧f , ⊧g)
    proof⇐HT rhs = (λ ⊧f → ((λ ⊧g → (p1 rhs) (⊧f , ⊧g)) ,
                            (λ ⊧g → (p2 rhs) (ht-to-c ⊧f , ⊧g)))) ,
                   proof⇐C (p2 rhs)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- f ⇒ g and f ⇒ j is equivalent to f ⇒ (g ∧ j)
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

-- ⊥ ∧ f is equivalent to ⊥
⊥∧eq⊥ : (f : F) → ValidHT ((⊥ ∧ f) ⇔ ⊥)
⊥∧eq⊥ f i@(IHT h t p) =
  let
    proof⇒C  lhs = p1 lhs
    proof⇒HT lhs = p1 lhs
    proof⇐C  rhs = Ø-elim rhs
    proof⇐HT rhs = Ø-elim rhs
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- ⊤ ⇒ ⊥ is equivalent to ⊥
fact⊥eq⊥ : ValidHT ((⊤ ⇒ ⊥) ⇔ ⊥)
fact⊥eq⊥ i@(IHT h t p) =
  let
    proof⇒C  lhs = lhs (λ ())
    proof⇒HT lhs = proof⇒C (p2 lhs)
    proof⇐C  rhs = λ _ → rhs
    proof⇐HT rhs = (λ _ → rhs) , proof⇐C rhs
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)
