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

-- rephrasing of property 1 for countermodels
-- <T,T> not⊧HT f implies <H,T> not⊧HT f
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
... | inl t⊧C¬f = inl (neg-c-to-ht {i} {f} t⊧C¬f)
... | inr t⊧C¬¬f = inr (neg-c-to-ht {i} {¬ f} t⊧C¬¬f)

-- hosoi axiom -----------------------------------------------------------------
-- f ∨ (f ⇒ g) ∨ ¬g
postulate hosoi : (f g : F) → ValidHT (f ∨ (f ⇒ g) ∨ (¬ g))
-- hosoi f g i@(IHT h t p) with weak-lem f i | weak-lem g i
-- ... | inl x | inl y = inr (inr y)
-- ... | inl (x1 , x2) | inr (y1 , y2) = inr (inl ((λ z → Ø-elim (x1 z)) , (λ z → Ø-elim (x2 z))))
-- ... | inr x | inl y = inr (inr y)
-- ... | inr (x1 , x2) | inr (y1 , y2) = {!!}

-- removal of nested implication -----------------------------------------------
-- (f ⇒ g) ⇒ g is equivalent to (g ∨ ¬f) ⇒ k and k ∨ f ∨ ¬g
-- lemma 1
-- TODO: reformulate with ValidHT
lem1-⇒1 : (f g k : F) → (i : IPHT) → i ⊧HT ((f ⇒ g) ⇒ k) → i ⊧HT ((g ∨ (¬ f)) ⇒ k)
lem1-⇒1 f g k i@(IHT h t p) s =
  let
    pht =  [ (λ y → (p1 s) ((λ _ → y) , (λ _ → total-ht-to-c (here-to-there {i} {g} y))) ) ,
             (λ (y1 , y2) → (p1 s) ((λ z → Ø-elim (y1 z)) , (λ z → Ø-elim (y2 z)))) ]
    pc =  [ (λ y → (p2 s) (λ _ → y)) ,
            (λ y → (p2 s) (λ z → Ø-elim (y z))) ]
  in
    (pht , pc)

lem1-⇒2 : (f g k : F) → (i : IPHT) → i ⊧HT ((f ⇒ g) ⇒ k) → i ⊧HT (k ∨ f ∨ (¬ g))
lem1-⇒2 f g k i@(IHT h t p) s with hosoi f g i
... | inl x = (inr (inl x))
... | inr (inl x) = (inl (p1 s x))
... | inr (inr x) = (inr (inr x))

lem1-⇒ : (f g k : F) → (i : IPHT) → i ⊧HT ((f ⇒ g) ⇒ k) → (i ⊧HT ((g ∨ (¬ f)) ⇒ k)) × (i ⊧HT (k ∨ f ∨ (¬ g)))
lem1-⇒ f g k i s = lem1-⇒1 f g k i s , lem1-⇒2 f g k i s

lem1-⇐ : (f g k : F) → (i : IPHT) → (i ⊧HT ((g ∨ (¬ f)) ⇒ k)) × (i ⊧HT (k ∨ f ∨ (¬ g))) → i ⊧HT ((f ⇒ g) ⇒ k)
lem1-⇐ f g k i@(IHT h t p) (s1 , inl s2) = (λ _ → s2) , (λ _ → total-ht-to-c (here-to-there {i} {k} s2))
lem1-⇐ f g k i@(IHT h t p) (s1 , inr (inl s2)) =
       (λ (x1 , x2) → (p1 s1) (inl (x1 s2))) , (λ x → (p2 s1) (inl (x (total-ht-to-c (here-to-there {i} {f} s2)))))
lem1-⇐ f g k i@(IHT h t p) (s1 , inr (inr s2)) =
       (λ (x1 , x2) → (p1 s1) (inr ((λ y → (p1 s2) (x1 y)) , (λ y → (p2 s2) (x2 y))))) , (λ x → (p2 s1) (inr (λ y → (p2 s2) (x y))))
