module HereAndThere.Equivalences where

open import Agda.Builtin.Equality using (refl)
open import Function using (id)
open import Data.Product using (_,_) renaming (proj₁ to p1 ; proj₂ to p2)
open import Data.Sum renaming (inj₁ to inl ; inj₂ to inr) using ()
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim) using()
open import Relation.Nullary using (Dec ; yes ; no)

open import HereAndThere.Base
open import HereAndThere.Properties
open import Formula.Decidable
open import Formula.Substitution

-- ⇔ is an equivalence relation ------------------------------------------------
-- forall f: f ⇔ f
refl⇔ : {f : F} → f ≡HT f
refl⇔ {f} i@(IHT h t p) =
  let
    proof⇒C  = id
    proof⇒HT = id
  in
    (proof⇒HT , proof⇒C) , (proof⇒HT , proof⇒C)

-- if f ⇔ g then g ⇔ f
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

-- combining implications to equivalence
-- if f ⇒ g and g ⇒ f then f ⇔ g
⇒⇐2⇔ : {f g : F} → ValidHT (f ⇒ g) → ValidHT (g ⇒ f) → f ≡HT g
⇒⇐2⇔ ⊧f⇒g ⊧g⇒f i = ⊧f⇒g i , ⊧g⇒f i

-- commutativity and associativity ---------------------------------------------
-- conjunction -----------------------------------
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

-- disjunction -----------------------------------
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

-- identities and zeroes -------------------------------------------------------
-- conjunction -----------------------------------
-- f ∧ ⊤ is equivalent to f
⊤-rid-∧ : {f : F} → (f ∧ ⊤) ≡HT f
⊤-rid-∧ {f} i@(IHT h t p) =
  let
    proof⇒C  ⊧f∧⊤ = p1 ⊧f∧⊤
    proof⇒HT ⊧f∧⊤ = p1 ⊧f∧⊤
    proof⇐C  ⊧f   = ⊧f , validC-⊤ t
    proof⇐HT ⊧f   = ⊧f , validHT-⊤ i
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- f ∧ ⊤ is equivalent to f
⊤-lid-∧ : {f : F} → (⊤ ∧ f) ≡HT f
⊤-lid-∧ {f} =
  ⊤ ∧ f ≡HT⟨ comm∧ ⟩
  f ∧ ⊤ ≡HT⟨ ⊤-rid-∧ ⟩
  f     ■

-- ⊥ ∧ f is equivalent to ⊥
⊥-lzero-∧ : {f : F} → (⊥ ∧ f) ≡HT ⊥
⊥-lzero-∧ {f} i@(IHT h t p) =
  let
    proof⇒C  ⊧⊥∧f = p1 ⊧⊥∧f
    proof⇒HT ⊧⊥∧f = p1 ⊧⊥∧f
    proof⇐C  ⊧⊥ = Ø-elim ⊧⊥
    proof⇐HT ⊧⊥ = Ø-elim ⊧⊥
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- f ∧ ⊥ is equivalent to ⊥
⊥-rzero-∧ : {f : F} → (f ∧ ⊥) ≡HT ⊥
⊥-rzero-∧ {f} =
  f ∧ ⊥ ≡HT⟨ comm∧ ⟩
  ⊥ ∧ f ≡HT⟨ ⊥-lzero-∧ ⟩
  ⊥     ■

-- disjunction -----------------------------------
-- f ∨ ⊥ is equivalent to f
⊥-rid-∨ : {f : F} → (f ∨ ⊥) ≡HT f
⊥-rid-∨ {f} i@(IHT h t p) =
  let
    proof⇒C  = λ { (inl ⊧f) → ⊧f
                 ; (inr ()) }
    proof⇒HT = λ { (inl ⊧f) → ⊧f
                 ; (inr ()) }
    proof⇐C  = λ ⊧f → inl ⊧f
    proof⇐HT = λ ⊧f → inl ⊧f
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- ⊥ ∨ f is equivalent to f
⊥-lid-∨ : {f : F} → (⊥ ∨ f) ≡HT f
⊥-lid-∨ {f} =
  ⊥ ∨ f ≡HT⟨ comm∨ ⟩
  f ∨ ⊥ ≡HT⟨ ⊥-rid-∨ ⟩
  f     ■

-- f ∨ ⊤ is equivalent to ⊤
⊤-rzero-∨ : {f : F} → (f ∨ ⊤) ≡HT ⊤
⊤-rzero-∨ {f} i@(IHT h t p) =
  let
    proof⇒C  = λ ⊧f∨⊤ → validC-⊤ t
    proof⇒HT = λ ⊧f∨⊤ → validHT-⊤ i
    proof⇐C  = λ ⊧⊤ → inr ⊧⊤
    proof⇐HT = λ ⊧⊤ → inr ⊧⊤
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- ⊤ ∨ f is equivalent to ⊤
⊤-lzero-∨ : {f : F} → (⊤ ∨ f) ≡HT ⊤
⊤-lzero-∨ {f} =
  ⊤ ∨ f ≡HT⟨ comm∨ ⟩
  f ∨ ⊤ ≡HT⟨ ⊤-rzero-∨ ⟩
  ⊤     ■

-- implication -----------------------------------
-- ⊤ ⇒ f is equivalent to f
⊤-lid-⇒ : {f : F} → (⊤ ⇒ f) ≡HT f
⊤-lid-⇒ {f} i@(IHT h t p) =
  let
    proof⇒C  ⊧⊤⇒f = ⊧⊤⇒f (validC-⊤ t)
    proof⇒HT ⊧⊤⇒f = (p1 ⊧⊤⇒f) (validHT-⊤ i)
    proof⇐C  ⊧f   = λ _ → ⊧f
    proof⇐HT ⊧f   = (λ _ → ⊧f) , proof⇐C (ht-to-c ⊧f)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- f ⇒ ⊤ is equivalent to ⊤
⊤-rzero-⇒ : {f : F} → (f ⇒ ⊤) ≡HT ⊤
⊤-rzero-⇒ {f} i@(IHT h t p) =
  let
    proof⇒C  ⊧f⇒⊤ = validC-⊤ t
    proof⇒HT ⊧f⇒⊤ = validHT-⊤ i
    proof⇐C  ⊧⊤ = λ _ → ⊧⊤
    proof⇐HT ⊧⊤ = (λ _ → ⊧⊤) ,
                  proof⇐C (p2 ⊧⊤)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- ⊥ ⇒ f is equivalent to ⊤
⊥-lzero-⇒ : {f : F} → (⊥ ⇒ f) ≡HT ⊤
⊥-lzero-⇒ {f} i@(IHT h t p) =
  let
    proof⇒C ⊧⊥⇒f = validC-⊤ t
    proof⇒HT ⊧⊥⇒f = validHT-⊤ i

    proof⇐C ⊧⊤ = λ ()
    proof⇐HT ⊧⊤ = (λ ()) , (λ ())
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- distributivity --------------------------------------------------------------
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

-- f ⇒ (g ∧ j) is equivalent to (f ⇒ g) ∧ (f ⇒ j)
distr⇒∧ : {f g j : F} → (f ⇒ (g ∧ j)) ≡HT ((f ⇒ g) ∧ (f ⇒ j))
distr⇒∧ {f} {g} {j} i@(IHT h t p) =
  let
    proof⇒C  ⊧f⇒g∧j   = (λ ⊧f → p1 (⊧f⇒g∧j ⊧f)) ,
                         (λ ⊧f → p2 (⊧f⇒g∧j ⊧f))
    proof⇒HT ⊧f⇒g∧j   = ((λ ⊧f → p1 ((p1 ⊧f⇒g∧j) ⊧f)) ,
                          (λ ⊧f → (p1 (proof⇒C (p2 ⊧f⇒g∧j))) ⊧f)) ,
                         ((λ ⊧f → p2 ((p1 ⊧f⇒g∧j) ⊧f)) ,
                          (λ ⊧f → (p2 (proof⇒C (p2 ⊧f⇒g∧j))) ⊧f))
    proof⇐C  ⊧f⇒g∧f⇒j = λ ⊧f → ((p1 ⊧f⇒g∧f⇒j) ⊧f ,
                                  (p2 ⊧f⇒g∧f⇒j) ⊧f)
    proof⇐HT ⊧f⇒g∧f⇒j = (λ ⊧f → ((p1 (p1 ⊧f⇒g∧f⇒j)) ⊧f ,
                                   (p1 (p2 ⊧f⇒g∧f⇒j)) ⊧f)) ,
                          (λ ⊧f → proof⇐C (p2 (p1 ⊧f⇒g∧f⇒j) ,
                                            p2 (p2 ⊧f⇒g∧f⇒j)) ⊧f)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- substitution ----------------------------------------------------------------
-- replacement of subformulas ...
-- ... in implication ----------------------------
-- if f ⇔ g then forall j: (j ⇒ f) ⇔ (j ⇒ g)
replace⇒rhs : {f g : F} → f ≡HT g → {j : F} → (j ⇒ f) ≡HT (j ⇒ g)
replace⇒rhs ⊧f⇔g {j} i@(IHT h t p) =
  let
    ⊧f⇒g , ⊧g⇒f = ⊧f⇔g i
    proof⇒C  ⊧j⇒f = λ ⊧j → (p2 ⊧f⇒g) (⊧j⇒f ⊧j)
    proof⇒HT ⊧j⇒f = ((λ ⊧j → (p1 ⊧f⇒g) ((p1 ⊧j⇒f) ⊧j)) ,
                       proof⇒C (p2 ⊧j⇒f))
    proof⇐C  ⊧j⇒g = λ ⊧j → (p2 ⊧g⇒f) (⊧j⇒g ⊧j)
    proof⇐HT ⊧j⇒g = ((λ ⊧j → (p1 ⊧g⇒f) ((p1 ⊧j⇒g) ⊧j)) ,
                      proof⇐C (p2 ⊧j⇒g))
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- if f ⇔ g then forall j: (f ⇒ j) ⇔ (g ⇒ j)
replace⇒lhs : {f g : F} → f ≡HT g → {j : F} → (f ⇒ j) ≡HT (g ⇒ j)
replace⇒lhs ⊧f⇔g {j} i@(IHT h t p) =
  let
    ⊧f⇒g , ⊧g⇒f = ⊧f⇔g i
    proof⇒C  ⊧f⇒j = λ ⊧g → ⊧f⇒j ((p2 ⊧g⇒f) ⊧g)
    proof⇒HT ⊧f⇒j = (λ ⊧g → (p1 ⊧f⇒j) ((p1 ⊧g⇒f) ⊧g)) ,
                      proof⇒C (p2 ⊧f⇒j)
    proof⇐C  ⊧g⇒j = λ ⊧f → ⊧g⇒j ((p2 ⊧f⇒g) ⊧f)
    proof⇐HT ⊧g⇒j = (λ ⊧f → (p1 ⊧g⇒j) ((p1 ⊧f⇒g) ⊧f)) ,
                      proof⇐C (p2 ⊧g⇒j)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- special case: in negation
-- if f ⇔ g then ¬f ⇔ ¬g
replace¬ : {f g : F} → f ≡HT g → ¬ f ≡HT ¬ g
replace¬ ⊧f⇔g = replace⇒lhs ⊧f⇔g {⊥}

-- ... in conjunction ----------------------------
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

-- ... in disjunction ----------------------------
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

-- general substitution --------------------------
-- if g⇔j then f ⇔ f[j/g]
subst≡HT : {f g j : F} → (e : g ≡HT j) → f ≡HT (f [ j / g ])
subst≡HT {f}     {g}  {j} g≡HTj with f ≡F? g
subst≡HT {f}     {.f} {j} f≡HTj | yes refl = f≡HTj
subst≡HT {⊥}     {g}  {j} g≡HTj | no _     = refl⇔
subst≡HT {V a}   {g}  {j} g≡HTj | no _     = refl⇔
subst≡HT {f ∧ k} {g}  {j} g≡HTj | no _     =
  f           ∧ k           ≡HT⟨ replace∧lhs (subst≡HT g≡HTj) ⟩
  f [ j / g ] ∧ k           ≡HT⟨ replace∧rhs (subst≡HT g≡HTj) ⟩
  f [ j / g ] ∧ k [ j / g ] ■
subst≡HT {f ∨ k} {g}  {j} g≡HTj | no _     =
  f           ∨ k           ≡HT⟨ replace∨lhs (subst≡HT g≡HTj) ⟩
  f [ j / g ] ∨ k           ≡HT⟨ replace∨rhs (subst≡HT g≡HTj) ⟩
  f [ j / g ] ∨ k [ j / g ] ■
subst≡HT {f ⇒ k} {g}  {j} g≡HTj | no _     =
  f           ⇒ k           ≡HT⟨ replace⇒lhs (subst≡HT g≡HTj) ⟩
  f [ j / g ] ⇒ k           ≡HT⟨ replace⇒rhs (subst≡HT g≡HTj) ⟩
  f [ j / g ] ⇒ k [ j / g ] ■
