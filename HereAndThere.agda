module HereAndThere where

open import Agda.Builtin.Equality
open import Data.Bool renaming (Bool to 𝔹 ; _∧_ to _∧𝔹_ ; _∨_ to _∨𝔹_ ; not to ¬𝔹)
open import Data.List using (List ; _∷_ ; [])
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim)
open import Data.Sum.Base using (_⊎_ ; [_,_]) renaming (inj₁ to inl ; inj₂ to inr)
open import Data.Product using (_×_ ; _,_) renaming (proj₁ to p1 ; proj₂ to p2)

open import Formula
open import Classical

-- here-and-there interpretations --------------------------------------------------------
-- ht interpretations consist of two classical interpretations h and t, s.t.
-- all atoms true in h are also true in t (h ⊆ t)
-- type for inclusion proofs
_⊆_ : IPC → IPC → Set
h ⊆ t = (a : Var) → h a ≡ true → t a ≡ true

-- ht interpretations
record IPHT : Set where
  constructor IHT
  field
    ph : IPC
    pt : IPC
    pi : ph ⊆ pt

open IPHT public

-- shorthand for total here-and-there interpretation
THT : IPC → IPHT
THT t = IHT t t (λ a p → p)

-- satisfiability of formulas in the logic of here-and-there -----------------------------
_⊧HT_ : IPHT → F → Set
i ⊧HT ⊥ = Ø
(IHT h _ _) ⊧HT (V a) = h a ≡ true
i ⊧HT (f ∧ g) = (i ⊧HT f) × (i ⊧HT g)
i ⊧HT (f ∨ g) = (i ⊧HT f) ⊎ (i ⊧HT g)
i@(IHT _ t _) ⊧HT (f ⇒ g) = ((i ⊧HT f) → (i ⊧HT g)) × (t ⊧C (f ⇒ g))

-- validity of formulas
ValidHT : F → Set
ValidHT f = (i : IPHT) → i ⊧HT f

-- extension of ⊧HT to theories
_⊨HT_ : IPHT → Th → Set
i ⊨HT t = (f : F) → f ∈ t → i ⊧HT f

-- total here-and-there interpretations collapse to classical logic ----------------------
-- i.e. <T,T> ⊧HT f iff T ⊧C f
-- ht satisfiability implies classical satisfiability
total-ht-to-c : {t : IPC} → {f : F} → ((THT t) ⊧HT f) → (t ⊧C f)
total-ht-to-c {t} {V a} s = s
total-ht-to-c {t} {f ∧ g} (sf , sg) = total-ht-to-c sf , total-ht-to-c sg
total-ht-to-c {t} {f ∨ g} (inl sf) = inl (total-ht-to-c sf)
total-ht-to-c {t} {f ∨ g} (inr sg) = inr (total-ht-to-c sg)
total-ht-to-c {t} {f ⇒ g} (sh , st) = st

-- classical satisfiability implies ht satisfiability
total-c-to-ht : {t : IPC} → {f : F} → (t ⊧C f) → ((THT t) ⊧HT f)
total-c-to-ht {t} {V a} s = s
total-c-to-ht {t} {f ∧ g} (sf , sg) = total-c-to-ht sf , total-c-to-ht sg
total-c-to-ht {t} {f ∨ g} (inl sf) = inl (total-c-to-ht sf)
total-c-to-ht {t} {f ∨ g} (inr sg) = inr (total-c-to-ht sg)
total-c-to-ht {t} {f ⇒ g} s = (λ t⊧HTf → total-c-to-ht (s (total-ht-to-c t⊧HTf))) , s

-- truth in the "here" implies true in the "there" ---------------------------------------
-- <H,T> ⊧HT f implies <T,T> ⊧HT f
-- (property 1)
here-to-there : {i : IPHT} → {f : F} → i ⊧HT f → (THT (pt i)) ⊧HT f
here-to-there {IHT h t p} {V a} s = p a s
here-to-there {IHT h t p} {f ∧ g} (sf , sg) = here-to-there sf , here-to-there sg
here-to-there {IHT h t p} {f ∨ g} (inl sf) = inl (here-to-there sf)
here-to-there {IHT h t p} {f ∨ g} (inr sg) = inr (here-to-there sg)
here-to-there {IHT h t p} {f ⇒ g} (_ , st) = total-c-to-ht st

-- <H,T> ⊧HT f implies T ⊧C f
here-to-c : {i : IPHT} → {f : F} → i ⊧HT f → (pt i) ⊧C f
here-to-c {i} {f} s = total-ht-to-c (here-to-there s)

-- rephrasing of property 1 for countermodels
-- <T,T> ⊭HT f implies <H,T> ⊭HT f
counter-there-to-here : {i : IPHT} → {f : F} → ((THT (pt i)) ⊧HT f → Ø) → i ⊧HT f → Ø
counter-there-to-here {i} {f} t⊭HTf i⊧HTf = t⊭HTf (here-to-there i⊧HTf)

-- negation in HT only depends on the "there" --------------------------------------------
-- <H,T> ⊧HT ¬f iff T ⊧C ¬f
-- (property 2)
neg-ht-to-c : {i : IPHT} → {f : F} → i ⊧HT (¬ f) → (pt i) ⊧C (¬ f)
neg-ht-to-c {IHT h t p} {f} (sh , st) = st

neg-c-to-ht : {i : IPHT} → {f : F} → (pt i) ⊧C (¬ f) → i ⊧HT (¬ f)
neg-c-to-ht {i@(IHT h t p)} {f} s =
  let
    t⊭HTf = λ t⊧HTf → s (total-ht-to-c t⊧HTf)
  in
    counter-there-to-here {i} {f} t⊭HTf , s

-- weak law of excluded middle -----------------------------------------------------------
-- ¬f ∨ ¬¬f
weak-lem : (f : F) → ValidHT ((¬ f) ∨ (¬ (¬ f)))
weak-lem f i@(IHT h t p) with lem (¬ f) t
... | inl t⊧C¬f  = inl (neg-c-to-ht {i} {f}   t⊧C¬f)
... | inr t⊧C¬¬f = inr (neg-c-to-ht {i} {¬ f} t⊧C¬¬f)

-- HT is three valued --------------------------------------------------------------------
-- 2 :  <H,T> ⊧HT f
-- 1 :  <H,T> ⊭HT f and  T ⊧C f
-- 0 : (<H,T> ⊭HT f and) T ⊭C f
3val : (f : F) → (i : IPHT) →
       (i ⊧HT f) ⊎ (((i ⊧HT f) → Ø) × ((pt i) ⊧C f)) ⊎ (((pt i) ⊧C f) → Ø)
3val ⊥ i = inr (inr (λ ()))
3val (V a) i@(IHT h t p) with h a
... | true  = inl refl
... | false with t a
...         | true  = inr (inl ((λ ()) , refl))
...         | false = inr (inr (λ ()))
3val (f ∧ g) i@(IHT h t p) with 3val f i | 3val g i
... | inl i⊧HTf | inl i⊧HTg =
  inl (i⊧HTf , i⊧HTg)
... | inl i⊧HTf | inr (inl (i⊭HTg , t⊧Cg)) =
  inr (inl ((λ (_ , i⊧HTg) → i⊭HTg i⊧HTg) , (here-to-c i⊧HTf , t⊧Cg)))
... | inl i⊧HTf | inr (inr t⊭Cg) =
  inr (inr (λ (_ , t⊧Cg) → t⊭Cg t⊧Cg))
... | inr (inl (i⊭HTf , t⊧Cf)) | inl i⊧HTg =
  inr (inl ((λ (i⊧HTf , _) → i⊭HTf i⊧HTf) , (t⊧Cf , here-to-c i⊧HTg)))
... | inr (inl (i⊭HTf , t⊧Cf)) | inr (inl (i⊭HTg , t⊧Cg)) =
  inr (inl ((λ (i⊧HTf , _) → i⊭HTf i⊧HTf) , (t⊧Cf , t⊧Cg)))
... | inr (inl (i⊭HTf , t⊧Cf)) | inr (inr t⊭Cg) =
  inr (inr (λ (_ , t⊧Cg) → t⊭Cg t⊧Cg))
... | inr (inr t⊭Cf) | _ =
  inr (inr (λ (t⊧Cf , _) → t⊭Cf t⊧Cf))
3val (f ∨ g) i@(IHT h t p) with 3val f i | 3val g i
... | inl i⊧HTf | _ =
  inl (inl i⊧HTf)
... | inr (inl (i⊭HTf , t⊧Cf)) | inl i⊧HTg =
  inl (inr i⊧HTg)
... | inr (inl (i⊭HTf , t⊧Cf)) | inr (inl (i⊭HTg , t⊧Cg)) =
  inr (inl ([ i⊭HTf , i⊭HTg ] , inr t⊧Cg))
... | inr (inl (i⊭HTf , t⊧Cf)) | inr (inr t⊭Cg) =
  inr (inl ([ i⊭HTf , (λ i⊧HTg → t⊭Cg (here-to-c i⊧HTg)) ] , inl t⊧Cf))
... | inr (inr t⊭Cf) | inl i⊧HTg =
  inl (inr i⊧HTg)
... | inr (inr t⊭Cf) | inr (inl (i⊭HTg , t⊧Cg)) =
  inr (inl ([ (λ i⊧HTf → t⊭Cf (here-to-c i⊧HTf)) , i⊭HTg ] , inr t⊧Cg))
... | inr (inr t⊭Cf) | inr (inr t⊭Cg) =
  inr (inr [ t⊭Cf , t⊭Cg ])
3val (f ⇒ g) i@(IHT h t p) with 3val f i | 3val g i
... | inl i⊧HTf | inl i⊧HTg =
  inl ((λ _ → i⊧HTg) , (λ _ → here-to-c i⊧HTg))
... | inl i⊧HTf | inr (inl (i⊭HTg , t⊧Cg)) =
  inr (inl ((λ (i⊧HTf⇒g , _) → i⊭HTg (i⊧HTf⇒g i⊧HTf)) , (λ _ → t⊧Cg)))
... | inl i⊧HTf | inr (inr t⊭Cg) =
  inr (inr (λ t⊧Cf⇒g → t⊭Cg (t⊧Cf⇒g (here-to-c i⊧HTf))))
... | inr (inl (i⊭HTf , t⊧Cf)) | inl i⊧HTg =
  inl ((λ _ → i⊧HTg) , (λ _ → here-to-c i⊧HTg))
... | inr (inl (i⊭HTf , t⊧Cf)) | inr (inl (i⊭HTg , t⊧Cg)) =
  inl ((λ i⊧HTf → Ø-elim (i⊭HTf i⊧HTf)) , (λ _ → t⊧Cg))
... | inr (inl (i⊭HTf , t⊧Cf)) | inr (inr t⊭Cg) =
  inr (inr (λ t⊧Cf⇒g → t⊭Cg (t⊧Cf⇒g t⊧Cf)))
... | inr (inr t⊭Cf) | _ =
  inl ((λ i⊧HTf → Ø-elim (t⊭Cf (here-to-c i⊧HTf))) , (λ t⊧Cf → Ø-elim (t⊭Cf t⊧Cf)))

-- hosoi axiom ---------------------------------------------------------------------------
-- f ∨ (f ⇒ g) ∨ ¬g
hosoi : (f g : F) → ValidHT (f ∨ (f ⇒ g) ∨ (¬ g))
hosoi f g i@(IHT h t p) with 3val f i
... | inl i⊧HTf      = inl i⊧HTf
... | inr (inr t⊭Cf) = inr (inl ((λ i⊧HTf → Ø-elim (t⊭Cf (here-to-c i⊧HTf))) ,
                                 (λ t⊧Cf → Ø-elim (t⊭Cf t⊧Cf))))
... | inr (inl (i⊭HTf , t⊧Cf)) with 3val g i
...   | inl i⊧HTg                = inr (inl ((λ _ → i⊧HTg) , (λ _ → here-to-c i⊧HTg)))
...   | inr (inl (i⊭HTg , t⊧Cg)) = inr (inl ((λ i⊧HTf → Ø-elim (i⊭HTf i⊧HTf)) ,
                                             (λ _ → t⊧Cg)))
...   | inr (inr t⊭Cg)           = inr (inr (neg-c-to-ht t⊭Cg))

-- some proofs on equivalences -----------------------------------------------------------
-- if f ⇒ g and g ⇒ f then f ⇔ g
⇒⇐2⇔ : {f g : F} → ValidHT (f ⇒ g) → ValidHT (g ⇒ f) → ValidHT (f ⇔ g)
⇒⇐2⇔ ⊧f⇒g ⊧g⇒f i = ⊧f⇒g i , ⊧g⇒f i

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
replace⇒rhs : {f g : F} → ValidHT (f ⇔ g) → (j : F) → ValidHT ((j ⇒ f) ⇔ (j ⇒ g))
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

-- if f ⇔ g then forall j: (f ∧ j) ⇔ (g ∧ j)
replace∧lhs : {f g : F} → ValidHT (f ⇔ g) → (j : F) → ValidHT ((f ∧ j) ⇔ (g ∧ j))
replace∧lhs ⊧f⇔g j i@(IHT h t p) =
  let
    ⊧f⇒g , ⊧g⇒f = ⊧f⇔g i
    proof⇒C  = λ (⊧f , ⊧j) → (p2 ⊧f⇒g) ⊧f , ⊧j
    proof⇒HT = λ (⊧f , ⊧j) → (p1 ⊧f⇒g) ⊧f , ⊧j
    proof⇐C  = λ (⊧g , ⊧j) → (p2 ⊧g⇒f) ⊧g , ⊧j
    proof⇐HT = λ (⊧g , ⊧j) → (p1 ⊧g⇒f) ⊧g , ⊧j
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- de morgan -----------------------------------------------------------------------------
-- ¬(f ∧ g) is equivalent to ¬f ∨ ¬g
-- ¬(f ∧ g) implies ¬f ∨ ¬g
demorgan⇒ : (f g : F) → ValidHT ((¬ (f ∧ g)) ⇒ ((¬ f) ∨ (¬ g)))
demorgan⇒ f g i@(IHT h t p) with hosoi f g i
... | inl i⊧HTf =
  let
    proofC  = λ t⊭Cf∧g → inr (λ t⊧Cg → t⊭Cf∧g (here-to-c i⊧HTf , t⊧Cg))
    proofHT = λ (i⊭HTf∧g , t⊭Cf∧g) → inr ((λ i⊧HTg → i⊭HTf∧g (i⊧HTf , i⊧HTg)) ,
                                          (λ t⊧Cg → t⊭Cf∧g (here-to-c i⊧HTf , t⊧Cg)))
  in
    proofHT , proofC
... | inr (inl (i⊧HTf⇒g , t⊧Cf⇒g)) =
  let
    proofC  = λ t⊭Cf∧g → inl (λ t⊧Cf → t⊭Cf∧g (t⊧Cf , t⊧Cf⇒g t⊧Cf))
    proofHT = λ (i⊭HTf∧g , t⊭Cf∧g) → inl ((λ i⊧HTf → i⊭HTf∧g (i⊧HTf , i⊧HTf⇒g i⊧HTf)) ,
                                          (λ t⊧Cf → t⊭Cf∧g (t⊧Cf , t⊧Cf⇒g t⊧Cf)))
  in
    proofHT , proofC
... | inr (inr (i⊭HTg , t⊭Cg)) =
  let
    proofC  = λ _ → inr t⊭Cg
    proofHT = λ _ → inr (i⊭HTg , t⊭Cg)
  in
    proofHT , proofC

-- ¬f ∨ ¬g implies ¬(f ∧ g)
demorgan⇐ : (f g : F) → ValidHT (((¬ f) ∨ (¬ g)) ⇒ (¬ (f ∧ g)))
demorgan⇐ f g i@(IHT h t p) =
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
demorgan : (f g : F) → ValidHT ((¬ (f ∧ g)) ⇔ ((¬ f) ∨ (¬ g)))
demorgan f g = ⇒⇐2⇔ (demorgan⇒ f g) (demorgan⇐ f g)

-- disjunctions in ht can be rewritten with implication ----------------------------------
-- f ∨ g is equivalent to ((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)
-- f ∨ g implies ((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)
∨2⇒-⇒ : (f g : F) → ValidHT ((f ∨ g) ⇒ (((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)))
∨2⇒-⇒ f g i@(IHT h t p) =
  let
    t⊧Cf⇒rhs  = λ t⊧Cf → ((λ t⊧Cf⇒g → t⊧Cf⇒g t⊧Cf) , (λ _ → t⊧Cf))
    i⊧HTf⇒rhs = λ i⊧HTf → (((λ (i⊧HTf⇒g , _) → i⊧HTf⇒g i⊧HTf) ,
                            p1 (t⊧Cf⇒rhs (here-to-c i⊧HTf))) ,
                           ((λ _ → i⊧HTf) ,
                            p2 (t⊧Cf⇒rhs (here-to-c i⊧HTf))))
    t⊧Cg⇒rhs  = λ t⊧Cg → ((λ _ → t⊧Cg) , (λ t⊧Cg⇒f → t⊧Cg⇒f t⊧Cg))
    i⊧HTg⇒rhs = λ i⊧HTg → (((λ _ → i⊧HTg) ,
                            p1 (t⊧Cg⇒rhs (here-to-c i⊧HTg))) ,
                           ((λ (i⊧HTg⇒f , _) → i⊧HTg⇒f i⊧HTg) ,
                            p2 (t⊧Cg⇒rhs (here-to-c i⊧HTg))))
  in
    ([ i⊧HTf⇒rhs , i⊧HTg⇒rhs ] , [ t⊧Cf⇒rhs , t⊧Cg⇒rhs ])

-- ((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f) implies f ∨ g
∨2⇒-⇐ : (f g : F) → ValidHT ((((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)) ⇒ (f ∨ g))
∨2⇒-⇐  f g i@(IHT h t p) with hosoi f g i
... | inl i⊧HTf =
  let
    proofC  = λ _ → inl (here-to-c i⊧HTf)
    proofHT = λ _ → inl i⊧HTf
  in
    proofHT , proofC
... | inr (inl i⊧HTf⇒g) =
  let
    proofC  = λ (t⊧C[f⇒g]⇒g  , _) → inr (t⊧C[f⇒g]⇒g (here-to-c i⊧HTf⇒g))
    proofHT = λ (i⊧HT[f⇒g]⇒g , _) → inr ((p1 i⊧HT[f⇒g]⇒g) i⊧HTf⇒g)
  in
    proofHT , proofC
... | inr (inr i⊧HT¬g) =
  let
    proofC  = λ (_ , t⊧C[g⇒f]⇒f)  → inl (t⊧C[g⇒f]⇒f (λ t⊧Cg → Ø-elim ((p2 i⊧HT¬g) t⊧Cg)))
    proofHT = λ (_ , i⊧HT[g⇒f]⇒f)
                → inl ((p1 i⊧HT[g⇒f]⇒f) ((λ i⊧HTg → Ø-elim ((p1 i⊧HT¬g) i⊧HTg)) ,
                                         (λ t⊧Cg → Ø-elim ((p2 i⊧HT¬g) t⊧Cg))))
  in
    proofHT , proofC

-- f ∨ g is equivalent to ((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)
∨2⇒ : (f g : F) → ValidHT ((f ∨ g) ⇔ (((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)))
∨2⇒ f g = ⇒⇐2⇔ (∨2⇒-⇒ f g) (∨2⇒-⇐ f g)

-- removal of nested implication ---------------------------------------------------------
-- (f ⇒ g) ⇒ k is equivalent to (g ∨ ¬f) ⇒ k and k ∨ f ∨ ¬g
-- (lemma 1)
-- (f ⇒ g) ⇒ k implies (g ∨ ¬f) ⇒ k
rem-nested⇒-⇒1 : (f g k : F) → ValidHT (((f ⇒ g) ⇒ k) ⇒ ((g ∨ (¬ f)) ⇒ k))
rem-nested⇒-⇒1 f g k i@(IHT h t p) =
  let
    proofC  lhs = [ (λ t⊧Cg → lhs (λ _ → t⊧Cg)) ,
                    (λ t⊭Cf → lhs (λ t⊧Cf → Ø-elim (t⊭Cf t⊧Cf))) ]
    proofHT lhs = [ (λ i⊧HTg  → (p1 lhs) ((λ _ → i⊧HTg) ,
                                          (λ _ → here-to-c i⊧HTg))) ,
                    (λ i⊧HT¬f → (p1 lhs) ((λ i⊧HTf → Ø-elim ((p1 i⊧HT¬f) i⊧HTf)) ,
                                          (λ t⊧Cf  → Ø-elim ((p2 i⊧HT¬f) t⊧Cf)))) ] ,
                  proofC (p2 lhs)
  in
    proofHT , proofC

-- (f ⇒ g) ⇒ k implies k ∨ f ∨ ¬g
rem-nested⇒-⇒2 : (f g k : F) → ValidHT (((f ⇒ g) ⇒ k) ⇒ (k ∨ f ∨ (¬ g)))
rem-nested⇒-⇒2 f g k i@(IHT h t p) with hosoi f g i
... | inl i⊧HTf =
  let
    proofC  = λ _ → inr (inl (here-to-c i⊧HTf))
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
rem-nested⇒-⇒ : (f g k : F) → ValidHT (((f ⇒ g) ⇒ k) ⇒ (((g ∨ (¬ f)) ⇒ k) ∧
                                                        (k ∨ f ∨ (¬ g))))
rem-nested⇒-⇒ f g k i@(IHT h t p) =
  ((λ i⊧HT[f⇒g]⇒k → ((p1 (rem-nested⇒-⇒1 f g k i)) i⊧HT[f⇒g]⇒k ,
                     (p1 (rem-nested⇒-⇒2 f g k i)) i⊧HT[f⇒g]⇒k)) ,
   (λ t⊧C[f⇒g]⇒k  → ((p2 (rem-nested⇒-⇒1 f g k i)) t⊧C[f⇒g]⇒k ,
                     (p2 (rem-nested⇒-⇒2 f g k i)) t⊧C[f⇒g]⇒k)))

-- (g ∨ ¬f) ⇒ k and k ∨ f ∨ ¬g implies (f ⇒ g) ⇒ k
rem-nested⇒-⇐ : (f g k : F) →
              ValidHT ((((g ∨ (¬ f)) ⇒ k) ∧ (k ∨ f ∨ (¬ g))) ⇒ ((f ⇒ g) ⇒ k))
rem-nested⇒-⇐ f g k i@(IHT h t p) =
  let
    proofC  =(λ where
                (t⊧C[g∨¬f]⇒k , inl t⊧Ck)
                  → (λ _ → t⊧Ck)
                (t⊧C[g∨¬f]⇒k , inr (inl t⊧Cf))
                  → (λ t⊧Cf⇒g → t⊧C[g∨¬f]⇒k (inl (t⊧Cf⇒g t⊧Cf)))
                (t⊧C[g∨¬f]⇒k , inr (inr t⊧C¬g))
                  → (λ t⊧Cf⇒g → t⊧C[g∨¬f]⇒k (inr (λ t⊧Cf → t⊧C¬g (t⊧Cf⇒g t⊧Cf)))))
    proofHT =(λ where
                (i⊧HT[g∨¬f]⇒k , inl i⊧HTk)
                  → ((λ _ → i⊧HTk) ,
                     (proofC (p2 i⊧HT[g∨¬f]⇒k ,
                              inl (here-to-c i⊧HTk))))
                (i⊧HT[g∨¬f]⇒k , inr (inl i⊧HTf))
                  → ((λ (i⊧HTf⇒g , _) → (p1 i⊧HT[g∨¬f]⇒k) (inl (i⊧HTf⇒g i⊧HTf))) ,
                     (proofC (p2 i⊧HT[g∨¬f]⇒k ,
                              inr (inl (here-to-c i⊧HTf)))))
                (i⊧HT[g∨¬f]⇒k , inr (inr i⊧HT¬g))
                  → ((λ (i⊧HTf⇒g , t⊧Cf⇒g)
                        → (p1 i⊧HT[g∨¬f]⇒k) (inr ((λ i⊧HTf
                                                     → (p1 i⊧HT¬g) (i⊧HTf⇒g i⊧HTf)) ,
                                                  (λ t⊧Cf
                                                     → (p2 i⊧HT¬g) (t⊧Cf⇒g t⊧Cf))))) ,
                     (proofC (p2 i⊧HT[g∨¬f]⇒k ,
                              inr (inr (p2 i⊧HT¬g))))))
  in
    proofHT , proofC

-- (f ⇒ g) ⇒ k is equivalent to (g ∨ ¬f) ⇒ k and k ∨ f ∨ ¬g
rem-nested⇒ : (f g k : F) → ValidHT (((f ⇒ g) ⇒ k) ⇔
                                     (((g ∨ (¬ f)) ⇒ k) ∧ (k ∨ f ∨ (¬ g))))
rem-nested⇒ f g k = ⇒⇐2⇔ (rem-nested⇒-⇒ f g k) (rem-nested⇒-⇐ f g k)

-- some equivalence proofs ---------------------------------------------------------------
-- f ⇒ (g ⇒ j) is equivalent to g ⇒ (f ⇒ j)
reorder⇒ : (f g j : F) → ValidHT ((f ⇒ (g ⇒ j)) ⇔ (g ⇒ (f ⇒ j)))
reorder⇒ f g j i@(IHT h t p) =
  let
    proof⇒C  lhs = λ ⊧g ⊧f → lhs ⊧f ⊧g
    proof⇒HT lhs = (λ ⊧g → ((λ ⊧f → (p1 ((p1 lhs) ⊧f)) ⊧g) ,
                            proof⇒C (p2 lhs) (here-to-c ⊧g))) ,
                   proof⇒C (p2 lhs)
    proof⇐C  rhs = λ ⊧f ⊧g → rhs ⊧g ⊧f
    proof⇐HT rhs = (λ ⊧f → ((λ ⊧g → (p1 ((p1 rhs) ⊧g)) ⊧f) ,
                            proof⇐C (p2 rhs) (here-to-c ⊧f))) ,
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
                            (λ ⊧g → (p2 rhs) (here-to-c ⊧f , ⊧g)))) ,
                   proof⇐C (p2 rhs)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- helper lemma for lemma 2
-- (f ⇒ g) ⇒ (j ⇒ k) is equivalent to ((j ∧ (g ∨ ¬f)) ⇒ k) ∧ (j ⇒ (k ∨ f ∨ ¬g))
f⇒f-eq-f∧f : (f g j k : F) →
             ValidHT (((f ⇒ g) ⇒ (j ⇒ k)) ⇔
                      (((j ∧ (g ∨ (¬ f))) ⇒ k) ∧ (j ⇒ (k ∨ (f ∨ (¬ g))))))
f⇒f-eq-f∧f f g j k =
  let
    lhs⇔j⇒[[f⇒g]⇒k] = reorder⇒ (f ⇒ g) j k
    ⇔j⇒[[[g∨¬f]⇒k]∧[k∨f∨¬g]] = replace⇒rhs (rem-nested⇒ f g k) j
    ⇔[j⇒[[g∨¬f]⇒k]]∧[j⇒[k∨f∨¬g]] = factor⇒∧ j ((g ∨ (¬ f)) ⇒ k) (k ∨ (f ∨ (¬ g)))
    ⇔rhs = replace∧lhs (uncurry j (g ∨ (¬ f)) k) (j ⇒ (k ∨ (f ∨ (¬ g))))
  in
    trans⇔ (trans⇔ (trans⇔ lhs⇔j⇒[[f⇒g]⇒k]
                               ⇔j⇒[[[g∨¬f]⇒k]∧[k∨f∨¬g]])
                               ⇔[j⇒[[g∨¬f]⇒k]]∧[j⇒[k∨f∨¬g]])
                               ⇔rhs
