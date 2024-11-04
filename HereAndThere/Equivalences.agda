module HereAndThere.Equivalences where

open import HereAndThere.Base
open import HereAndThere.Properties

-- ⇔ is an equivalence relation ------------------------------------------------
refl⇔ : {f : F} → f ≡HT f
refl⇔ {f} i@(IHT h t p) =
  let
    proof⇒C  ⊧f = ⊧f
    proof⇒HT ⊧f = ⊧f
  in
    (proof⇒HT , proof⇒C) , (proof⇒HT , proof⇒C)

symm⇔ : {f g : F} → f ≡HT g → g ≡HT f
symm⇔ f⇔g i@(IHT h t p) =
  let
    ⊧f⇒g , ⊧g⇒f = f⇔g i
  in
    ⊧g⇒f , ⊧f⇒g

-- if f ⇔ g and g ⇔ j then f ⇔ j
trans⇔ : {f g j : F} → f ≡HT g → g ≡HT j → f ≡HT j
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

-- equational reasoning for ht equivalences
infix  2 _■
infixr 1 _≡HT⟨def⟩_ _≡HT⟨_⟩_ _≡HT⟨_⟩ˢ_

_≡HT⟨def⟩_ : (f {g} : F) → f ≡HT g → f ≡HT g
_ ≡HT⟨def⟩ f≡HTg = f≡HTg

_≡HT⟨_⟩_ : (f {g j} : F) → f ≡HT g → g ≡HT j → f ≡HT j
_ ≡HT⟨ f≡HTg ⟩ g≡HTj = trans⇔ f≡HTg g≡HTj

_≡HT⟨_⟩ˢ_ : (f {g j} : F) → g ≡HT f → g ≡HT j → f ≡HT j
_ ≡HT⟨ g≡HTf ⟩ˢ g≡HTj = trans⇔ (symm⇔ g≡HTf) g≡HTj

_■ : (f : F) → f ≡HT f
_ ■ = refl⇔

-- basic properties of ⇒ -------------------------------------------------------
-- if f ⇔ g then forall j: (j ⇒ f) ⇔ (j ⇒ g)
replace⇒rhs : {f g : F} → f ≡HT g → {j : F} → (j ⇒ f) ≡HT (j ⇒ g)
replace⇒rhs ⊧f⇔g {j} i@(IHT h t p) =
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
replace⇒lhs : {f g : F} → f ≡HT g → {j : F} → (f ⇒ j) ≡HT (g ⇒ j)
replace⇒lhs ⊧f⇔g {j} i@(IHT h t p) =
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

⊤-lid-⇒ : {f : F} → (⊤ ⇒ f) ≡HT f
⊤-lid-⇒ {f} i@(IHT h t p) =
  let
    proof⇒C  ⊧⊤⇒f = ⊧⊤⇒f (λ ())
    proof⇒HT ⊧⊤⇒f = (p1 ⊧⊤⇒f) ((λ ()) , (λ ()))
    proof⇐C  ⊧f   = λ _ → ⊧f
    proof⇐HT ⊧f   = (λ _ → ⊧f) , proof⇐C (ht-to-c ⊧f)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- combining implications to equivalence
-- if f ⇒ g and g ⇒ f then f ⇔ g
⇒⇐2⇔ : {f g : F} → ValidHT (f ⇒ g) → ValidHT (g ⇒ f) → f ≡HT g
⇒⇐2⇔ ⊧f⇒g ⊧g⇒f i = ⊧f⇒g i , ⊧g⇒f i

-- basic properties of ∧ -------------------------------------------------------
-- f ∧ g is equivalent to g ∧ f
comm∧ : {f g : F} → (f ∧ g) ≡HT (g ∧ f)
comm∧ {f} {g} i@(IHT h t p) =
  let
    proof⇒C  ⊧f∧g = (p2 ⊧f∧g) , (p1 ⊧f∧g)
    proof⇒HT ⊧f∧g = (p2 ⊧f∧g) , (p1 ⊧f∧g)
    proof⇐C  ⊧g∧f = (p2 ⊧g∧f) , (p1 ⊧g∧f)
    proof⇐HT ⊧g∧f = (p2 ⊧g∧f) , (p1 ⊧g∧f)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- (f ∧ g) ∧ j is equivalent to f ∧ (g ∧ j)
assoc∧ : {f g j : F} → ((f ∧ g) ∧ j) ≡HT (f ∧ (g ∧ j))
assoc∧ {f} {g} {j} i@(IHT h t p) =
  let
    proof⇒C  = λ ((⊧f , ⊧g) , ⊧j) → (⊧f , (⊧g , ⊧j))
    proof⇒HT = λ ((⊧f , ⊧g) , ⊧j) → (⊧f , (⊧g , ⊧j))
    proof⇐C  = λ (⊧f , (⊧g , ⊧j)) → ((⊧f , ⊧g) , ⊧j)
    proof⇐HT = λ (⊧f , (⊧g , ⊧j)) → ((⊧f , ⊧g) , ⊧j)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- if f ⇔ g then forall j: (f ∧ j) ⇔ (g ∧ j)
replace∧lhs : {f g : F} → f ≡HT g → {j : F} → (f ∧ j) ≡HT (g ∧ j)
replace∧lhs ⊧f⇔g {j} i@(IHT h t p) =
  let
    ⊧f⇒g , ⊧g⇒f = ⊧f⇔g i
    proof⇒C  = λ (⊧f , ⊧j) → (p2 ⊧f⇒g) ⊧f , ⊧j
    proof⇒HT = λ (⊧f , ⊧j) → (p1 ⊧f⇒g) ⊧f , ⊧j
    proof⇐C  = λ (⊧g , ⊧j) → (p2 ⊧g⇒f) ⊧g , ⊧j
    proof⇐HT = λ (⊧g , ⊧j) → (p1 ⊧g⇒f) ⊧g , ⊧j
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- if f ⇔ g then forall j: (j ∧ f) ⇔ (j ∧ g)
replace∧rhs : {f g : F} → f ≡HT g → {j : F} → (j ∧ f) ≡HT (j ∧ g)
replace∧rhs {f} {g} f≡HTg {j} =
  j ∧ f ≡HT⟨ comm∧ ⟩
  f ∧ j ≡HT⟨ replace∧lhs f≡HTg ⟩
  g ∧ j ≡HT⟨ comm∧ ⟩
  j ∧ g ■

-- f is equivalent to f ∧ ⊤
⊤-rid-∧ : {f : F} → (f ∧ ⊤) ≡HT f
⊤-rid-∧ {f} i@(IHT h t p) =
  let
    proof⇒C  ⊧f∧⊤ = p1 ⊧f∧⊤
    proof⇒HT ⊧f∧⊤ = p1 ⊧f∧⊤
    proof⇐C  ⊧f   = ⊧f , (λ ())
    proof⇐HT ⊧f   = ⊧f , ((λ ()) , (λ ()))
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- f is equivalent to ⊤ ∧ f
⊤-lid-∧ : {f : F} → (⊤ ∧ f) ≡HT f
⊤-lid-∧ {f} =
  ⊤ ∧ f ≡HT⟨ comm∧ ⟩
  f ∧ ⊤ ≡HT⟨ ⊤-rid-∧ ⟩
  f     ■

-- basic properties of ∨ -------------------------------------------------------
-- f ∨ g is equivalent to g ∨ f
comm∨ : {f g : F} → (f ∨ g) ≡HT (g ∨ f)
comm∨ {f} {g} i@(IHT h t p) =
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

-- (f ∨ g) ∨ j is equivalent to f ∨ (g ∨ j)
assoc∨ : {f g j : F} → ((f ∨ g) ∨ j) ≡HT (f ∨ (g ∨ j))
assoc∨ {f} {g} {j} i@(IHT h t p) =
  let
    proof⇒C  = λ { (inl (inl ⊧f)) → inl ⊧f
                 ; (inl (inr ⊧g)) → inr (inl ⊧g)
                 ; (inr ⊧j)       → inr (inr ⊧j) }
    proof⇒HT = λ { (inl (inl ⊧f)) → inl ⊧f
                 ; (inl (inr ⊧g)) → inr (inl ⊧g)
                 ; (inr ⊧j)       → inr (inr ⊧j) }
    proof⇐C  = λ { (inl ⊧f)       → inl (inl ⊧f)
                 ; (inr (inl ⊧g)) → inl (inr ⊧g)
                 ; (inr (inr ⊧j)) → inr ⊧j }
    proof⇐HT = λ { (inl ⊧f)       → inl (inl ⊧f)
                 ; (inr (inl ⊧g)) → inl (inr ⊧g)
                 ; (inr (inr ⊧j)) → inr ⊧j }
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- if f ⇔ g then forall j: (f ∨ j) ⇔ (g ∨ j)
replace∨lhs : {f g : F} → f ≡HT g → {j : F} → (f ∨ j) ≡HT (g ∨ j)
replace∨lhs ⊧f⇔g {j} i@(IHT h t p) =
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
replace∨rhs : {f g : F} → f ≡HT g → {j : F} → (j ∨ f) ≡HT (j ∨ g)
replace∨rhs {f} {g} f≡HTg {j} =
  j ∨ f ≡HT⟨ comm∨ ⟩
  f ∨ j ≡HT⟨ replace∨lhs f≡HTg ⟩
  g ∨ j ≡HT⟨ comm∨ ⟩
  j ∨ g ■

-- properties of ⇒ -------------------------------------------------------------
-- f ⇒ (g ⇒ j) is equivalent to g ⇒ (f ⇒ j)
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

-- ⊤ ⇒ ⊥ is equivalent to ⊥
fact⊥eq⊥ : (⊤ ⇒ ⊥) ≡HT ⊥
fact⊥eq⊥ = ⊤-lid-⇒

-- properties of ¬ -------------------------------------------------------------
-- ¬¬¬f is equivalent to ¬f
reduce3¬ : {f : F} → (¬ (¬ (¬ f))) ≡HT (¬ f)
reduce3¬ {f} i@(IHT h t p) =
  let
    (proof⇒C , proof⇐C) = reduce2¬ {¬ f} t
    proof⇒HT = λ (_ , ⊧C¬¬f) → neg-c-to-ht (proof⇒C ⊧C¬¬f)
    proof⇐HT = λ (_ , ⊧C¬f)  → neg-c-to-ht (proof⇐C ⊧C¬f)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- properties of ∧ -------------------------------------------------------------
-- ⊥ ∧ f is equivalent to ⊥
⊥∧eq⊥ : {f : F} → (⊥ ∧ f) ≡HT ⊥
⊥∧eq⊥ {f} i@(IHT h t p) =
  let
    proof⇒C  lhs = p1 lhs
    proof⇒HT lhs = p1 lhs
    proof⇐C  rhs = Ø-elim rhs
    proof⇐HT rhs = Ø-elim rhs
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- properties of ∧ and ∨ -------------------------------------------------------
-- f ∧ (g ∨ j) is equivalent to (f ∧ g) ∨ (f ∧ j)
distr∧∨ : {f g j : F} → (f ∧ (g ∨ j)) ≡HT ((f ∧ g) ∨ (f ∧ j))
distr∧∨ {f} {g} {j} i@(IHT h t p) =
  let
    proof⇒C  = λ { (⊧f , inl ⊧g) → inl (⊧f , ⊧g)
                 ; (⊧f , inr ⊧j) → inr (⊧f , ⊧j) }
    proof⇒HT = λ { (⊧f , inl ⊧g) → inl (⊧f , ⊧g)
                 ; (⊧f , inr ⊧j) → inr (⊧f , ⊧j) }
    proof⇐C  = λ { (inl (⊧f , ⊧g)) → (⊧f , inl ⊧g)
                 ; (inr (⊧f , ⊧j)) → (⊧f , inr ⊧j) }
    proof⇐HT = λ { (inl (⊧f , ⊧g)) → (⊧f , inl ⊧g)
                 ; (inr (⊧f , ⊧j)) → (⊧f , inr ⊧j) }
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- f ∨ (g ∧ j) is equivalent to (f ∨ g) ∧ (f ∨ j)
distr∨∧ : {f g j : F} → (f ∨ (g ∧ j)) ≡HT ((f ∨ g) ∧ (f ∨ j))
distr∨∧ {f} {g} {j} i@(IHT h t p) =
  let
    proof⇒C  = λ { (inl ⊧f)        → (inl ⊧f , inl ⊧f)
                 ; (inr (⊧g , ⊧j)) → (inr ⊧g , inr ⊧j) }
    proof⇒HT = λ { (inl ⊧f)        → (inl ⊧f , inl ⊧f)
                 ; (inr (⊧g , ⊧j)) → (inr ⊧g , inr ⊧j) }
    proof⇐C  = λ { (inl ⊧f , _)      → inl ⊧f
                 ; (inr _  , inl ⊧f) → inl ⊧f
                 ; (inr ⊧g , inr ⊧j) → inr (⊧g , ⊧j) }
    proof⇐HT = λ { (inl ⊧f , _)      → inl ⊧f
                 ; (inr _  , inl ⊧f) → inl ⊧f
                 ; (inr ⊧g , inr ⊧j) → inr (⊧g , ⊧j) }
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- properties of ⇒ and ∧ -------------------------------------------------------
-- f ⇒ (g ∧ j) is equivalent to (f ⇒ g) ∧ (f ⇒ j)
distr⇒∧ : {f g j : F} → (f ⇒ (g ∧ j)) ≡HT ((f ⇒ g) ∧ (f ⇒ j))
distr⇒∧ {f} {g} {j} i@(IHT h t p) =
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
uncurry : {f g j : F} → (f ⇒ (g ⇒ j)) ≡HT ((f ∧ g) ⇒ j)
uncurry {f} {g} {j} i@(IHT h t p) =
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
