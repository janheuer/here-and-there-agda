module HereAndThere where

open import Agda.Builtin.Equality
open import Data.Bool renaming (Bool to 𝔹 ; _∧_ to _∧𝔹_ ; _∨_ to _∨𝔹_ ; not to ¬𝔹)
open import Data.List using (List ; _∷_ ; [])
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim)
open import Data.Sum.Base using (_⊎_ ; [_,_]) renaming (inj₁ to inl ; inj₂ to inr)
open import Data.Product using (_×_ ; _,_) renaming (proj₁ to p1 ; proj₂ to p2)

open import Formula
open import Classical

-- here-and-there interpretations ----------------------------------------------
-- two classical interpretations and an inclusion proof
data IPHT : Set where
  IHT : (h t : IPC) → ((a : Var) → (h a ≡ true) → (t a ≡ true)) → IPHT
-- shorthand for total here-and-there interpretation
THT : IPC → IPHT
THT t = IHT t t (λ a p → p)
-- projections to extract the components of a ht interpretation
ph : IPHT → IPC
ph (IHT h t p) = h

pt : IPHT → IPC
pt (IHT h t p) = t

pi : (i : IPHT) → ((a : Var) → ((ph i) a ≡ true) → ((pt i) a ≡ true))
pi (IHT h t p) = p

-- satisfiability of formulas in the logic of here-and-there -------------------
_⊧HT_ : IPHT → F → Set
i ⊧HT ⊥ = Ø
(IHT h _ _) ⊧HT (V a) = h a ≡ true
i ⊧HT (f ∧ g) = (i ⊧HT f) × (i ⊧HT g)
i ⊧HT (f ∨ g) = (i ⊧HT f) ⊎ (i ⊧HT g)
i@(IHT _ t _) ⊧HT (f ⇒ g) = ((i ⊧HT f) → (i ⊧HT g)) × (t ⊧C (f ⇒ g))

ValidHT : F → Set
ValidHT f = (i : IPHT) → i ⊧HT f

-- total here-and-there interpretations collapse to classical logic ------------
-- i.e. <T,T> ⊧HT F iff T ⊧C F
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

-- truth in the "here" implies true in the "there" -----------------------------
-- <H,T> ⊧HT f implies <T,T> ⊧HT f
-- (property 1)
here-to-there : {i : IPHT} → {f : F} → i ⊧HT f → (THT (pt i)) ⊧HT f
here-to-there {IHT _ _ p} {V a} s = p a s
here-to-there {i} {f ∧ g} (sf , sg) = here-to-there sf , here-to-there sg
here-to-there {i} {f ∨ g} (inl sf) = inl (here-to-there sf)
here-to-there {i} {f ∨ g} (inr sg) = inr (here-to-there sg)
here-to-there {IHT _ _ _} {f ⇒ g} (_ , st) = total-c-to-ht st

here-to-c : {i : IPHT} → {f : F} → i ⊧HT f → (pt i) ⊧C f
here-to-c {i} {f} s = total-ht-to-c (here-to-there s)

-- rephrasing of property 1 for countermodels
-- <T,T> ⊭HT f implies <H,T> ⊭HT f
counter-there-to-here : {i : IPHT} → {f : F} → ((THT (pt i)) ⊧HT f → Ø) → i ⊧HT f → Ø
counter-there-to-here {i} {f} t⊭HTf i⊧HTf = t⊭HTf (here-to-there i⊧HTf)

-- negation in HT only depends on the "there" ----------------------------------
-- <H,T> ⊧HT ¬f iff T ⊧C ¬f
-- property 2
neg-ht-to-c : {i : IPHT} → {f : F} → i ⊧HT (¬ f) → (pt i) ⊧C (¬ f)
neg-ht-to-c {IHT h t p} {f} (sh , st) = st

neg-c-to-ht : {i : IPHT} → {f : F} → (pt i) ⊧C (¬ f) → i ⊧HT (¬ f)
neg-c-to-ht {i@(IHT h t p)} {f} s =
  let
    t⊭HTf = λ t⊧HTf → s (total-ht-to-c t⊧HTf)
  in
    counter-there-to-here {i} {f} t⊭HTf , s

-- weak law of excluded middle -------------------------------------------------
-- ¬f ∨ ¬¬f
weak-lem : (f : F) → ValidHT ((¬ f) ∨ (¬ (¬ f)))
weak-lem f i@(IHT h t p) with lem (¬ f) t
... | inl t⊧C¬f  = inl (neg-c-to-ht {i} {f}   t⊧C¬f)
... | inr t⊧C¬¬f = inr (neg-c-to-ht {i} {¬ f} t⊧C¬¬f)

-- hosoi axiom -----------------------------------------------------------------
-- f ∨ (f ⇒ g) ∨ ¬g
hosoi : (f g : F) → ValidHT (f ∨ (f ⇒ g) ∨ (¬ g))
hosoi f g i@(IHT h t p) with weak-lem g i | weak-lem f i
... | inl i⊧HT¬g  | _ = inr (inr i⊧HT¬g)
... | inr i⊧HT¬¬g | inl (i⊧HT¬f , t⊧C¬f) =
  let
    i⊧HTf⇒g = λ i⊧HTf → Ø-elim (i⊧HT¬f i⊧HTf)
    t⊧Cf⇒g  = λ t⊧Cf  → Ø-elim (t⊧C¬f  t⊧Cf)
  in
    inr (inl (i⊧HTf⇒g , t⊧Cf⇒g))
... | inr (i⊧HT¬¬g , t⊧C¬¬g) | inr (i⊧HT¬¬f , t⊧C¬¬f) = {!!}

-- removal of nested implication -----------------------------------------------
-- (f ⇒ g) ⇒ k is equivalent to (g ∨ ¬f) ⇒ k and k ∨ f ∨ ¬g
-- lemma 1
-- (f ⇒ g) ⇒ k implies (g ∨ ¬f) ⇒ k
rem-nested⇒1 : (f g k : F) → (i : IPHT) → i ⊧HT ((f ⇒ g) ⇒ k) → i ⊧HT ((g ∨ (¬ f)) ⇒ k)
rem-nested⇒1 f g k i@(IHT h t p) (sht , sc) =
  let
    i⊧HTg⇒k = λ i⊧HTg → sht ((λ _ → i⊧HTg) ,
                             (λ _ → (here-to-c i⊧HTg)))
    i⊧HT¬f⇒k = λ (i⊧HT¬f , t⊧C¬f) → sht ((λ i⊧HTf → Ø-elim (i⊧HT¬f i⊧HTf)) ,
                                         (λ t⊧Cf → Ø-elim (t⊧C¬f t⊧Cf)))
    pht =  [ i⊧HTg⇒k , i⊧HT¬f⇒k ]
    t⊧Cg⇒k = λ t⊧Cg → sc (λ _ → t⊧Cg)
    t⊧C¬f⇒k = λ t⊧C¬f → sc (λ t⊧Cf → Ø-elim (t⊧C¬f t⊧Cf))
    pc =  [ t⊧Cg⇒k , t⊧C¬f⇒k ]
  in
    (pht , pc)

-- (f ⇒ g) ⇒ k implies k ∨ f ∨ ¬g
rem-nested⇒2 : (f g k : F) → (i : IPHT) → i ⊧HT ((f ⇒ g) ⇒ k) → i ⊧HT (k ∨ f ∨ (¬ g))
rem-nested⇒2 f g k i@(IHT h t p) s with hosoi f g i
... | inl i⊧HTf = (inr (inl i⊧HTf))
... | inr (inl i⊧HTf⇒g) = (inl (p1 s i⊧HTf⇒g))
... | inr (inr i⊧HT¬g) = (inr (inr i⊧HT¬g))

-- (f ⇒ g) ⇒ k implies (g ∨ ¬f) ⇒ k and k ∨ f ∨ ¬g
rem-nested⇒ : (f g k : F) → (i : IPHT) → i ⊧HT ((f ⇒ g) ⇒ k) → (i ⊧HT ((g ∨ (¬ f)) ⇒ k)) × (i ⊧HT (k ∨ f ∨ (¬ g)))
rem-nested⇒ f g k i s = rem-nested⇒1 f g k i s , rem-nested⇒2 f g k i s

-- (g ∨ ¬f) ⇒ k and k ∨ f ∨ ¬g implies (f ⇒ g) ⇒ k
add-nested⇒ : (f g k : F) → (i : IPHT) → (i ⊧HT ((g ∨ (¬ f)) ⇒ k)) × (i ⊧HT (k ∨ f ∨ (¬ g))) → i ⊧HT ((f ⇒ g) ⇒ k)
add-nested⇒ f g k i@(IHT h t p) (s1 , inl i⊧HTk) = (λ _ → i⊧HTk) , (λ _ → here-to-c i⊧HTk)
add-nested⇒ f g k i@(IHT h t p) (s1 , inr (inl i⊧HTf)) =
  let
    i⊧HTg∨¬f⇒k = p1 s1
    t⊧Cg∨¬f⇒k = p2 s1
    pht = (λ (i⊧HTf⇒g , t⊧Cf⇒g) → i⊧HTg∨¬f⇒k (inl (i⊧HTf⇒g i⊧HTf)))
    pc = (λ t⊧Cf⇒g → t⊧Cg∨¬f⇒k (inl (t⊧Cf⇒g (here-to-c i⊧HTf))))
  in
    (pht , pc)
add-nested⇒ f g k i@(IHT h t p) (s1 , inr (inr i⊧HT¬g)) =
  let
    i⊧HTg∨¬f⇒k = p1 s1
    t⊧Cg∨¬f⇒k = p2 s1
    pht = λ (i⊧HTf⇒g , t⊧Cf⇒g) → i⊧HTg∨¬f⇒k (inr ((λ i⊧HTf → (p1 i⊧HT¬g) (i⊧HTf⇒g i⊧HTf)) ,
                                                   (λ t⊧Cf → (p2 i⊧HT¬g) (t⊧Cf⇒g t⊧Cf))))
    pc = λ t⊧Cf⇒g → t⊧Cg∨¬f⇒k (inr (λ t⊧Cf → (p2 i⊧HT¬g) (t⊧Cf⇒g t⊧Cf)))
  in
    (pht , pc)
