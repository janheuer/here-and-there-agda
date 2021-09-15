module HereAndThereEval where

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
open import HereAndThere using (IPHT ; IHT ; THT ; pt ; _⊧HT_)

-- satisfiability of formulas in the logic of here-and-there -----------------------------
evalHT : IPHT → F → 𝔹
evalHT _ ⊥ = false
evalHT (IHT h _ _) (V a) = h a
evalHT i (f ∧ g) = (evalHT i f) ∧𝔹 (evalHT i g)
evalHT i (f ∨ g) = (evalHT i f) ∨𝔹 (evalHT i g)
evalHT i@(IHT h t p) (f ⇒ g) = ((evalHT i f) ⇒𝔹 (evalHT i g)) ∧𝔹 (evalC t (f ⇒ g))

infix 22 _⊧HTe_

_⊧HTe_ : IPHT → F → Set
i ⊧HTe f = evalHT i f ≡ true

-- equivalence proof ---------------------------------------------------------------------
⊧HT-to-⊧HTe : {i : IPHT} → {f : F} → i ⊧HT f → i ⊧HTe f
⊧HTe-to-⊧HT : {i : IPHT} → {f : F} → i ⊧HTe f → i ⊧HT f

⊧HT-to-⊧HTe {IHT h t p} {V a} s = s
⊧HT-to-⊧HTe {i} {f ∧ g} (sf , sg) = ×-to-∧𝔹 (⊧HT-to-⊧HTe sf , ⊧HT-to-⊧HTe sg)
⊧HT-to-⊧HTe {i} {f ∨ g} (inl sf) = ⊎-to-∨𝔹 (inl (⊧HT-to-⊧HTe sf))
⊧HT-to-⊧HTe {i} {f ∨ g} (inr sg) = ⊎-to-∨𝔹 (inr (⊧HT-to-⊧HTe sg))
⊧HT-to-⊧HTe {IHT h t p} {f ⇒ g} (sh , st) =
  let
    i⊧HTef⇒g = λ i⊧HTef → ⊧HT-to-⊧HTe (sh (⊧HTe-to-⊧HT i⊧HTef))
  in
    ×-to-∧𝔹 (→-to-⇒𝔹 i⊧HTef⇒g , ⊧C-to-⊧Ce st)

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
    i⊧HTf⇒g = λ i⊧HTf → ⊧HTe-to-⊧HT ((⇒𝔹-to-→ sh) (⊧HT-to-⊧HTe i⊧HTf))
  in
    (i⊧HTf⇒g , ⊧Ce-to-⊧C st)

-- total here-and-there interpretations collapse to classical logic ----------------------
-- i.e. <T,T> ⊧HT F iff T ⊧C F
-- ht satisfiability implies classical satisfiability
total-ht-to-c : (t : IPC) → (f : F) → (b : 𝔹) → ((evalHT (THT t) f) ≡ b) → ((evalC t f) ≡ b)
total-ht-to-c t ⊥ false s = s
total-ht-to-c t (V a) _ s = s
total-ht-to-c t (f ∧ g) true s =
  let
    (sf , sg) = ∧𝔹-to-× s
  in
    ×-to-∧𝔹 (total-ht-to-c t f true sf , total-ht-to-c t g true sg)
total-ht-to-c t (f ∧ g) false u with ∧𝔹-to-⊎ u
... | inl uf = ⊎-to-∧𝔹 (inl (total-ht-to-c t f false uf))
... | inr ug = ⊎-to-∧𝔹 (inr (total-ht-to-c t g false ug))
total-ht-to-c t (f ∨ g) true s with ∨𝔹-to-⊎ s
... | inl sf = ⊎-to-∨𝔹 (inl (total-ht-to-c t f true sf))
... | inr sg = ⊎-to-∨𝔹 (inr (total-ht-to-c t g true sg))
total-ht-to-c t (f ∨ g) false u =
  let
    (uf , ug) = ∨𝔹-to-× u
  in
    ×-to-∨𝔹 (total-ht-to-c t f false uf , total-ht-to-c t g false ug)
total-ht-to-c t (f ⇒ g) true s = p2 (∧𝔹-to-× s)
total-ht-to-c t (f ⇒ g) false u with ∧𝔹-to-⊎ u
... | inl uh = ×-to-∨𝔹 (¬𝔹-t-f (total-ht-to-c t f true
                                              (remove-¬𝔹 (¬𝔹-f-t (p1 (∨𝔹-to-× uh))))) ,
                        total-ht-to-c t g false (p2 (∨𝔹-to-× uh)))
... | inr ut = ut

-- classical satisfiability implies ht satisfiability
total-c-to-ht : (t : IPC) → (f : F) → (b : 𝔹) → ((evalC t f) ≡ b) → ((evalHT (THT t) f) ≡ b)
total-c-to-ht t ⊥ false s = s
total-c-to-ht t (V a) _ s = s
total-c-to-ht t (f ∧ g) true s =
  let
    (sf , sg) = ∧𝔹-to-× s
  in
    ×-to-∧𝔹 (total-c-to-ht t f true sf , total-c-to-ht t g true sg)
total-c-to-ht t (f ∧ g) false u with ∧𝔹-to-⊎ u
... | inl uf = ⊎-to-∧𝔹 (inl (total-c-to-ht t f false uf))
... | inr ug = ⊎-to-∧𝔹 (inr (total-c-to-ht t g false ug))
total-c-to-ht t (f ∨ g) true s with ∨𝔹-to-⊎ s
... | inl sf = ⊎-to-∨𝔹 (inl (total-c-to-ht t f true sf))
... | inr sg = ⊎-to-∨𝔹 (inr (total-c-to-ht t g true sg))
total-c-to-ht t (f ∨ g) false u =
  let
    (uf , ug) = ∨𝔹-to-× u
  in
    ×-to-∨𝔹 (total-c-to-ht t f false uf , total-c-to-ht t g false ug)
total-c-to-ht t (f ⇒ g) true s with ⇒𝔹-to-⊎ s
... | inl uf = ×-to-∧𝔹 (⊎-to-∨𝔹 (inl (¬𝔹-f-t (total-c-to-ht t f false uf))), s)
... | inr sg = ×-to-∧𝔹 (⊎-to-∨𝔹 (inr (total-c-to-ht t g true sg)) , s)
total-c-to-ht t (f ⇒ g) false u = ⊎-to-∧𝔹 (inr u)

-- truth in the "here" implies true in the "there" ---------------------------------------
-- <H,T> ⊧HT f implies <T,T> ⊧HT f
-- (property 1)
here-to-there : (i : IPHT) → (f : F) → ((evalHT i f) ≡ true) → ((evalHT (THT (pt i)) f) ≡ true)
here-to-there i@(IHT h t p) (V a) s = p a s
here-to-there i@(IHT h t p) (f ∧ g) s =
  let
    (sf , sg) = ∧𝔹-to-× s
  in
    ×-to-∧𝔹 (here-to-there i f sf , here-to-there i g sg)
here-to-there i@(IHT h t p) (f ∨ g) s with ∨𝔹-to-⊎ s
... | inl sf = ⊎-to-∨𝔹 (inl (here-to-there i f sf))
... | inr sg = ⊎-to-∨𝔹 (inr (here-to-there i g sg))
here-to-there i@(IHT h t p) (f ⇒ g) s = total-c-to-ht t (f ⇒ g) true (p2 (∧𝔹-to-× s))

-- rephrasing of property 1 for countermodels
-- <T,T> ⊭HT f implies <H,T> ⊭HT f
counter-there-to-here : (t : IPC) → (f : F) → ((evalHT (THT t) f) ≡ false) → ((h : IPC) → (p : (a : Var) → (h a ≡ true) → (t a ≡ true)) → ((evalHT (IHT h t p) f) ≡ false))
counter-there-to-here t f c h p = contra {evalHT (IHT h t p) f} {evalHT (THT t) f} (here-to-there (IHT h t p) f) c
