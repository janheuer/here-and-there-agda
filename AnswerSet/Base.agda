module AnswerSet.Base where

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using (List ; [] ; _∷_)
open import Data.Sum renaming (inj₁ to inl ; inj₂ to inr) using (_⊎_)
open import Data.Product renaming (proj₁ to p1 ; proj₂ to p2) using (_×_ ; _,_)
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim) using ()

open import Formula public
open import Classical public
open import HereAndThere public
open import Equilibrium public

-- definition of reduct on propositional formulas ------------------------------
reduct : F → IPC → F
reduct f i with dec-C f i
...              | inr i⊭f = ⊥
reduct (V a) i   | inl i⊧f = V a
reduct (f ∧ g) i | inl i⊧f = (reduct f i) ∧ (reduct g i)
reduct (f ∨ g) i | inl i⊧f = (reduct f i) ∨ (reduct g i)
reduct (f ⇒ g) i | inl i⊧f = (reduct f i) ⇒ (reduct g i)

-- definition of stable models of propositional formulas using the reduct ------
min-c : IPC → F → Set
min-c i f = (j : IPC) → (j ⊆ i) → (j ⊧C f) → j ≡ i

_⊧SM_ : IPC → F → Set
i ⊧SM f = (i ⊧C (reduct f i)) × (min-c i (reduct f i))

-- relationship ht and reduct --------------------------------------------------
reduct-to-ht : {i : IPHT} → {f : F} → (ph i ⊧C (reduct f (pt i))) → i ⊧HT f

ht-to-reduct : {i : IPHT} → {f : F} → (i ⊧HT f) → (ph i ⊧C (reduct f (pt i)))

reduct-to-ht {i@(IHT h t p)} {ϕ} h⊧Cϕ^t with dec-C ϕ t
reduct-to-ht {i@(IHT h t p)} {V a} h⊧Ca^t | inl t⊧Ca =
  h⊧Ca^t
reduct-to-ht {i@(IHT h t p)} {f ∧ g} (h⊧Cf^t , h⊧Cg^t) | inl t⊧Cf∧g =
  reduct-to-ht h⊧Cf^t , reduct-to-ht h⊧Cg^t
reduct-to-ht {i@(IHT h t p)} {f ∨ g} (inl h⊧Cf^t) | inl t⊧Cf∨g =
  inl (reduct-to-ht h⊧Cf^t)
reduct-to-ht {i@(IHT h t p)} {f ∨ g} (inr h⊧Cg^t) | inl t⊧Cf∨g =
  inr (reduct-to-ht h⊧Cg^t)
reduct-to-ht {i@(IHT h t p)} {f ⇒ g} h⊧Cf⇒g^t | inl t⊧Cf⇒g = proof
  where
    i⊧HTf→i⊧HTg = λ i⊧HTf → reduct-to-ht (h⊧Cf⇒g^t (ht-to-reduct i⊧HTf))
    proof = i⊧HTf→i⊧HTg , t⊧Cf⇒g

ht-to-reduct {i@(IHT h t p)} {ϕ} i⊧HTϕ with dec-C ϕ t
ht-to-reduct {i@(IHT h t p)} {ϕ} i⊧HTϕ | inr t⊭Cϕ = proof
  where
    t⊧HTϕ = here-to-there i⊧HTϕ
    t⊧Cϕ = total-ht-to-c t⊧HTϕ
    proof = t⊭Cϕ t⊧Cϕ
ht-to-reduct {i@(IHT h t p)} {V a} i⊧HTa | inl t⊧Ca =
  i⊧HTa
ht-to-reduct {i@(IHT h t p)} {f ∧ g} (i⊧HTf , i⊧HTg) | inl t⊧Cf∧g =
  ht-to-reduct i⊧HTf , ht-to-reduct i⊧HTg
ht-to-reduct {i@(IHT h t p)} {f ∨ g} (inl i⊧HTf) | inl t⊧Cf∨g =
  inl (ht-to-reduct i⊧HTf)
ht-to-reduct {i@(IHT h t p)} {f ∨ g} (inr i⊧HTg) | inl t⊧Cf∨g =
  inr (ht-to-reduct i⊧HTg)
ht-to-reduct {i@(IHT h t p)} {f ⇒ g} i⊧HTf⇒g | inl t⊧Cf⇒g = proof
  where
    i⊧HTf→i⊧HTg = p1 i⊧HTf⇒g
    proof = λ h⊧Cf^t → ht-to-reduct {i} {g} (i⊧HTf→i⊧HTg (reduct-to-ht h⊧Cf^t))

-- relationship equilibrium models and stable model ----------------------------
eq-to-sm : {i : IPC} → {f : F} → (i ⊧EQ f) → i ⊧SM f
eq-to-sm {i} {f} (i⊧HTf , i-min-h) = i⊧Cf^i , i-min-c
  where
    i⊧Cf^i = ht-to-reduct i⊧HTf
    i-min-c = λ j j⊆i j⊧Cf^i → i-min-h j j⊆i (reduct-to-ht j⊧Cf^i)

sm-to-eq : {i : IPC} → {f : F} → (i ⊧SM f) → i ⊧EQ f
sm-to-eq {i} {f} (i⊧Cf^i , i-min-c) = i⊧HTf , i-min-h
  where
    i⊧HTf = reduct-to-ht i⊧Cf^i
    i-min-h = λ j j⊆i j⊧HTf → i-min-c j j⊆i (ht-to-reduct j⊧HTf)
