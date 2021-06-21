module HereAndThere where

open import Agda.Builtin.Equality
open import Data.Nat
open import Data.Bool renaming (Bool to 𝔹 ; _∧_ to _∧𝔹_ ; _∨_ to _∨𝔹_ ; not to ¬𝔹)
open import Data.List using (List ; _∷_ ; [])
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim)
open import Data.Sum.Base using (_⊎_ ; [_,_]) renaming (inj₁ to inl ; inj₂ to inr)
open import Data.Product using (_×_ ; _,_) renaming (proj₁ to p1 ; proj₂ to p2)

open import BoolHelper
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
evalHT : IPHT → F → 𝔹
evalHT _ ⊥ = false
evalHT (IHT h _ _) (V a) = h a
evalHT i (f ∧ g) = (evalHT i f) ∧𝔹 (evalHT i g)
evalHT i (f ∨ g) = (evalHT i f) ∨𝔹 (evalHT i g)
evalHT i@(IHT h t p) (f ⇒ g) = ((evalHT i f) ⇒𝔹 (evalHT i g)) ∧𝔹 (evalC t (f ⇒ g))

infix 22 _⊧HTe_

_⊧HTe_ : IPHT → F → Set
i ⊧HTe f = evalHT i f ≡ true

-- total here-and-there interpretations collapse to classical logic ------------
-- i.e. <T,T> ⊧HT F iff T ⊧C F
-- ht satisfiability implies classical satisfiability
total-ht-to-c : (t : IPC) → (f : F) → (b : 𝔹) → ((evalHT (THT t) f) ≡ b) → ((evalC t f) ≡ b)
total-ht-to-c t ⊥ false s = s
total-ht-to-c t (V a) _ s = s
total-ht-to-c t (f ∧ g) true s =
              ×-to-∧𝔹 (total-ht-to-c t f true (p1 (∧𝔹-to-× s)) ,
                       total-ht-to-c t g true (p2 (∧𝔹-to-× s)))
total-ht-to-c t (f ∧ g) false s with ∧𝔹-to-⊎ s
... | inl p = ⊎-to-∧𝔹 (inl (total-ht-to-c t f false p))
... | inr p = ⊎-to-∧𝔹 (inr (total-ht-to-c t g false p))
total-ht-to-c t (f ∨ g) true s with ∨𝔹-to-⊎ s
... | inl p = ⊎-to-∨𝔹 (inl (total-ht-to-c t f true p))
... | inr p = ⊎-to-∨𝔹 (inr (total-ht-to-c t g true p))
total-ht-to-c t (f ∨ g) false s =
              ×-to-∨𝔹 (total-ht-to-c t f false (p1 (∨𝔹-to-× s)) ,
                       total-ht-to-c t g false (p2 (∨𝔹-to-× s)))
total-ht-to-c t (f ⇒ g) true s = p2 (∧𝔹-to-× s)
total-ht-to-c t (f ⇒ g) false s with ∧𝔹-to-⊎ s
... | inl p = ×-to-∨𝔹 (¬𝔹-t-f (total-ht-to-c t f true
                                             (remove-¬𝔹 (¬𝔹-f-t (p1 (∨𝔹-to-× p))))) ,
                       total-ht-to-c t g false (p2 (∨𝔹-to-× p)))
... | inr p = p

-- classical satisfiability implies ht satisfiability
total-c-to-ht : (t : IPC) → (f : F) → (b : 𝔹) → ((evalC t f) ≡ b) → ((evalHT (THT t) f) ≡ b)
total-c-to-ht t ⊥ false s = s
total-c-to-ht t (V a) _ s = s
total-c-to-ht t (f ∧ g) true s =
              ×-to-∧𝔹 (total-c-to-ht t f true (p1 (∧𝔹-to-× s)) ,
                       total-c-to-ht t g true (p2 (∧𝔹-to-× s)))
total-c-to-ht t (f ∧ g) false s with ∧𝔹-to-⊎ s
... | inl p = ⊎-to-∧𝔹 (inl (total-c-to-ht t f false p))
... | inr p = ⊎-to-∧𝔹 (inr (total-c-to-ht t g false p))
total-c-to-ht t (f ∨ g) true s with ∨𝔹-to-⊎ s
... | inl p = ⊎-to-∨𝔹 (inl (total-c-to-ht t f true p))
... | inr p = ⊎-to-∨𝔹 (inr (total-c-to-ht t g true p))
total-c-to-ht t (f ∨ g) false s =
              ×-to-∨𝔹 (total-c-to-ht t f false (p1 (∨𝔹-to-× s)) ,
                       total-c-to-ht t g false (p2 (∨𝔹-to-× s)))
total-c-to-ht t (f ⇒ g) true s with ⇒𝔹-to-⊎ s
... | inl p = ×-to-∧𝔹 (⊎-to-∨𝔹 (inl (¬𝔹-f-t (total-c-to-ht t f false p))), s)
... | inr p = ×-to-∧𝔹 (⊎-to-∨𝔹 (inr (total-c-to-ht t g true p)) , s)
total-c-to-ht t (f ⇒ g) false s = ⊎-to-∧𝔹 (inr s)

-- truth in the "here" implies true in the "there" -----------------------------
-- <H,T> ⊧HT f implies <T,T> ⊧HT f
-- (property 1)
here-to-there : (i : IPHT) → (f : F) → ((evalHT i f) ≡ true) → ((evalHT (THT (pt i)) f) ≡ true)
here-to-there i@(IHT h t p) (V a) s = p a s
here-to-there i@(IHT h t p) (f ∧ g) s =
              ×-to-∧𝔹 (here-to-there i f (p1 (∧𝔹-to-× s)) ,
                       here-to-there i g (p2 (∧𝔹-to-× s)))
here-to-there i@(IHT h t p) (f ∨ g) s with ∨𝔹-to-⊎ s
... | inl d = ⊎-to-∨𝔹 (inl (here-to-there i f d))
... | inr d = ⊎-to-∨𝔹 (inr (here-to-there i g d))
here-to-there i@(IHT h t p) (f ⇒ g) s = total-c-to-ht t (f ⇒ g) true (p2 (∧𝔹-to-× s))

-- rephrasing of property 1 for countermodels
-- <T,T> not⊧HT f implies <H,T> not⊧HT f
counter-there-to-here : (t : IPC) → (f : F) → ((evalHT (THT t) f) ≡ false) → ((h : IPC) → (p : (a : Var) → (h a ≡ true) → (t a ≡ true)) → ((evalHT (IHT h t p) f) ≡ false))
counter-there-to-here t f c h p = contra (evalHT (IHT h t p) f) (evalHT (THT t) f) (here-to-there (IHT h t p) f) c

-- alternative model definitions -----------------------------------------------
_⊧HT_ : IPHT → F → Set
i ⊧HT ⊥ = Ø
(IHT h _ _) ⊧HT (V a) = h a ≡ true
i ⊧HT (f ∧ g) = (i ⊧HT f) × (i ⊧HT g)
i ⊧HT (f ∨ g) = (i ⊧HT f) ⊎ (i ⊧HT g)
i@(IHT _ t _) ⊧HT (f ⇒ g) = ((i ⊧HT f) → (i ⊧HT g)) × (t ⊧C (f ⇒ g))

-- equivalence proof
⊧HT-to-⊧HTe : {i : IPHT} → {f : F} → i ⊧HT f → i ⊧HTe f
⊧HTe-to-⊧HT : {i : IPHT} → {f : F} → i ⊧HTe f → i ⊧HT f

⊧HT-to-⊧HTe {IHT h t p} {V a} s = s
⊧HT-to-⊧HTe {i} {f ∧ g} (sf , sg) = ×-to-∧𝔹 (⊧HT-to-⊧HTe sf , ⊧HT-to-⊧HTe sg)
⊧HT-to-⊧HTe {i} {f ∨ g} (inl sf) = ⊎-to-∨𝔹 (inl (⊧HT-to-⊧HTe sf))
⊧HT-to-⊧HTe {i} {f ∨ g} (inr sg) = ⊎-to-∨𝔹 (inr (⊧HT-to-⊧HTe sg))
⊧HT-to-⊧HTe {IHT h t p} {f ⇒ g} (sh , st) = ×-to-∧𝔹 (→-to-⇒𝔹 (λ sef → ⊧HT-to-⊧HTe (sh (⊧HTe-to-⊧HT sef))) , ⊧C-to-⊧Ce st)

⊧HTe-to-⊧HT {IHT h t p} {V a} s = s
⊧HTe-to-⊧HT {i} {f ∧ g} s =
  let
    (sf , sg) = ∧𝔹-to-× s
  in
    (⊧HTe-to-⊧HT sf , ⊧HTe-to-⊧HT sg)
⊧HTe-to-⊧HT {i} {f ∨ g} s with ∨𝔹-to-⊎ s
... | inl sf = inl (⊧HTe-to-⊧HT sf)
... | inr sg = inr (⊧HTe-to-⊧HT sg)
⊧HTe-to-⊧HT {IHT h t p} {f ⇒ g} s =
  let
    (sh , st) = ∧𝔹-to-× s
  in
    ((λ x → ⊧HTe-to-⊧HT ((⇒𝔹-to-→ sh) (⊧HT-to-⊧HTe x))) , ⊧Ce-to-⊧C st)

-- for total interpretations ht and c are equivalent
total-h-c : {t : IPC} → {f : F} → ((THT t) ⊧HT f) → (t ⊧C f)
total-h-c {t} {V a} s = s
total-h-c {t} {f ∧ g} (sf , sg) = total-h-c sf , total-h-c sg
total-h-c {t} {f ∨ g} (inl s) = inl (total-h-c s)
total-h-c {t} {f ∨ g} (inr s) = inr (total-h-c s)
total-h-c {t} {f ⇒ g} s = p2 s

total-c-h : {t : IPC} → {f : F} → (t ⊧C f) → ((THT t) ⊧HT f)
total-c-h {t} {V a} s = s
total-c-h {t} {f ∧ g} (sf , sg) = total-c-h sf , total-c-h sg
total-c-h {t} {f ∨ g} (inl s) = inl (total-c-h s)
total-c-h {t} {f ∨ g} (inr s) = inr (total-c-h s)
total-c-h {t} {f ⇒ g} s = (λ x → total-c-h (s (total-h-c x))) , s

-- property 1
h-to-t : (i : IPHT) → (f : F) → i ⊧HT f → (THT (pt i)) ⊧HT f
h-to-t (IHT h _ p) (V a) s = p a s
h-to-t i (f ∧ g) (sf , sg) = h-to-t i f sf , h-to-t i g sg
h-to-t i (f ∨ g) (inl sf) = inl (h-to-t i f sf)
h-to-t i (f ∨ g) (inr sg) = inr (h-to-t i g sg)
h-to-t (IHT _ t _) (f ⇒ g) (_ , st) = total-c-h st

counter-t-to-h : {t : IPC} → {f : F} → ((THT t) ⊧HT f → Ø) → (h : IPC) → (p : (a : Var) → h a ≡ true → t a ≡ true) → (IHT h t p) ⊧HT f → Ø
counter-t-to-h {t} {f} c h p m = c (h-to-t (IHT h t p) f m)

-- property 2
neg-h-c : (i : IPHT) → (f : F) → i ⊧HT (¬ f) → (pt i) ⊧C (¬ f)
neg-h-c (IHT h t p) f (sh , st) = st

neg-c-h : (i : IPHT) → (f : F) → (pt i) ⊧C (¬ f) → i ⊧HT (¬ f)
neg-c-h (IHT h t p) f n = counter-t-to-h {t} {f} (λ s → n (total-h-c {t} {f} s)) h p , n

-- ¬f ∨ ¬¬f
weak-lem : (f : F) → (i : IPHT) → i ⊧HT ((¬ f) ∨ (¬ (¬ f)))
weak-lem f (IHT h t p) with lem (¬ f) t
... | inl x = inl (neg-c-h (IHT h t p) f x)
... | inr x = inr (neg-c-h (IHT h t p) (¬ f) x)

-- f ∨ (f ⇒ g) ∨ ¬g
postulate hosoi : (f g : F) → (i : IPHT) → i ⊧HT (f ∨ (f ⇒ g) ∨ (¬ g))
-- hosoi f g i@(IHT h t p) with weak-lem f i | weak-lem g i
-- ... | inl x | inl y = inr (inr y)
-- ... | inl (x1 , x2) | inr (y1 , y2) = inr (inl ((λ z → Ø-elim (x1 z)) , (λ z → Ø-elim (x2 z))))
-- ... | inr x | inl y = inr (inr y)
-- ... | inr (x1 , x2) | inr (y1 , y2) = {!!}

-- lemma 1
lem1-⇒1 : (f g k : F) → (i : IPHT) → i ⊧HT ((f ⇒ g) ⇒ k) → i ⊧HT ((g ∨ (¬ f)) ⇒ k)
lem1-⇒1 f g k i@(IHT h t p) s =
  let
    pht =  [ (λ y → (p1 s) ((λ _ → y) , (λ _ → total-h-c (h-to-t i g y))) ) ,
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
lem1-⇐ f g k i@(IHT h t p) (s1 , inl s2) = (λ _ → s2) , (λ _ → total-h-c (h-to-t i k s2))
lem1-⇐ f g k i@(IHT h t p) (s1 , inr (inl s2)) =
       (λ (x1 , x2) → (p1 s1) (inl (x1 s2))) , (λ x → (p2 s1) (inl (x (total-h-c (h-to-t i f s2)))))
lem1-⇐ f g k i@(IHT h t p) (s1 , inr (inr s2)) =
       (λ (x1 , x2) → (p1 s1) (inr ((λ y → (p1 s2) (x1 y)) , (λ y → (p2 s2) (x2 y))))) , (λ x → (p2 s1) (inr (λ y → (p2 s2) (x y))))
