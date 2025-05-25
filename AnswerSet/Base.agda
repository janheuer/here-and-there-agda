module AnswerSet.Base where

-- definition of answer sets/stable models using reducts on arbitrary
-- propositional formulas
-- equivalence to equilibrium models

open import Agda.Builtin.Equality using (_≡_)
open import Function using (id)
open import Relation.Binary.PropositionalEquality using (subst)
open import Data.Bool renaming (Bool to 𝔹) using (true)
open import Data.List using (List ; [] ; _∷_)
open import Data.Sum renaming (inj₁ to inl ; inj₂ to inr) using (_⊎_)
open import Data.Product renaming (proj₁ to p1 ; proj₂ to p2) using (_×_ ; _,_)
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim) using ()
import Relation.Binary.PropositionalEquality.Properties as Eq
open Eq.≡-Reasoning

open import Formula public
open import Classical public
open import HereAndThere public
open import Equilibrium public

-- definition of reduct on propositional formulas ------------------------------
reduct : F → IPC → F
reduct f i with dec-C f i
-- if i is not a classical model the reduct is ⊥
...              | inr i⊭f = ⊥
-- otherwise we go by the formula structure
-- for atoms we do not change anything
reduct (V a) i   | inl i⊧f = V a
-- for the recursive cases we build the reducts of the sub-formulas
-- and then connect them with the same connective again
reduct (f ∧ g) i | inl i⊧f = (reduct f i) ∧ (reduct g i)
reduct (f ∨ g) i | inl i⊧f = (reduct f i) ∨ (reduct g i)
reduct (f ⇒ g) i | inl i⊧f = (reduct f i) ⇒ (reduct g i)

-- definition of stable models of propositional formulas using the reduct ------
-- minimal classical model
min-c : IPC → F → Set
min-c i f = (j : IPC) → (j ⊆ i) → (j ⊧C f) → j ≡ i

_⊧SM_ : IPC → F → Set
-- 1) i is a model of the reduct
-- 2) i is the minimal model of the reduct
i ⊧SM f = (i ⊧C (reduct f i)) × (min-c i (reduct f i))

-- relationship ht and reduct --------------------------------------------------
-- given a ht interpretation <h,t> and a formula f the following are equivalent
-- 1) <h,t> is a ht model of f
-- 2) h is a classical model of the reduct of f with respect to t
-- the proofs are mutually recursive
reduct-to-ht : {i : IPHT} → {f : F} → (ph i ⊧C (reduct f (pt i))) → i ⊧HT f

ht-to-reduct : {i : IPHT} → {f : F} → (i ⊧HT f) → (ph i ⊧C (reduct f (pt i)))

-- we start by checking whether t is a classical model of the formula
-- as this is the first step to computing the reduct
reduct-to-ht {i@(IHT h t p)} {ϕ} h⊧Cϕ^t with dec-C ϕ t
-- we do not have to consider the case where it is not a model as then
-- h can not be a classical model of the reduct
reduct-to-ht {i@(IHT h t p)} {V a} h⊧Ca | inl t⊧Ca = subst id h⊧Ca≡i⊧HTa h⊧Ca
  -- note that here the reduct of (V a) is exactly (V a)
  where
    h⊧Ca≡i⊧HTa = h ⊧C (V a)  ≡⟨⟩
                 h a ≡ true  ≡⟨⟩
                 i ⊧HT (V a) ∎
reduct-to-ht {i@(IHT h t p)} {f ∧ g} (h⊧Cf^t , h⊧Cg^t) | inl t⊧Cf∧g =
  reduct-to-ht h⊧Cf^t , reduct-to-ht h⊧Cg^t
reduct-to-ht {i@(IHT h t p)} {f ∨ g} (inl h⊧Cf^t) | inl t⊧Cf∨g =
  inl (reduct-to-ht h⊧Cf^t)
reduct-to-ht {i@(IHT h t p)} {f ∨ g} (inr h⊧Cg^t) | inl t⊧Cf∨g =
  inr (reduct-to-ht h⊧Cg^t)
reduct-to-ht {i@(IHT h t p)} {f ⇒ g} h⊧Cf⇒g^t | inl t⊧Cf⇒g = proof
  -- we already have the classical proof component
  -- we only have to construct the ht component
  where
    i⊧HTf→i⊧HTg : i ⊧HT f → i ⊧HT g
    i⊧HTf→i⊧HTg i⊧HTf = i⊧HTg
      where
        -- h is a classical model of the reduct of f
        h⊧Cf^t = ht-to-reduct i⊧HTf
        -- thus h is also a classical model of the reduct of g
        -- because we know that h is a model of the reduct of f ⇒ g
        h⊧Cg^t = h⊧Cf⇒g^t h⊧Cf^t
        -- then i is also a ht model of g
        i⊧HTg = reduct-to-ht h⊧Cg^t
    proof = i⊧HTf→i⊧HTg , t⊧Cf⇒g

-- we again start by checking if t is a classical model of the formula
ht-to-reduct {i@(IHT h t p)} {ϕ} i⊧HTϕ with dec-C ϕ t
-- if t is not a model we can derive a contradiction
ht-to-reduct {i@(IHT h t p)} {ϕ} i⊧HTϕ | inr t⊭Cϕ = proof
  where
    -- as <h,t> is a ht model of ϕ, <t,t> is also a ht model of ϕ
    t⊧HTϕ = here-to-there i⊧HTϕ
    -- as <t,t> is a ht model of ϕ, t is also a classical model
    t⊧Cϕ = total-ht-to-c t⊧HTϕ
    -- this leads to a contradiction
    proof = t⊭Cϕ t⊧Cϕ
ht-to-reduct {i@(IHT h t p)} {V a} i⊧HTa | inl t⊧Ca = subst id i⊧HTa≡h⊧Ca i⊧HTa
  where
    i⊧HTa≡h⊧Ca = i ⊧HT (V a) ≡⟨⟩
                 h a ≡ true  ≡⟨⟩
                 h ⊧C (V a)  ∎
ht-to-reduct {i@(IHT h t p)} {f ∧ g} (i⊧HTf , i⊧HTg) | inl t⊧Cf∧g =
  ht-to-reduct i⊧HTf , ht-to-reduct i⊧HTg
ht-to-reduct {i@(IHT h t p)} {f ∨ g} (inl i⊧HTf) | inl t⊧Cf∨g =
  inl (ht-to-reduct i⊧HTf)
ht-to-reduct {i@(IHT h t p)} {f ∨ g} (inr i⊧HTg) | inl t⊧Cf∨g =
  inr (ht-to-reduct i⊧HTg)
ht-to-reduct {i@(IHT h t p)} {f ⇒ g} i⊧HTf⇒g | inl t⊧Cf⇒g = proof
  where
    i⊧HTf→i⊧HTg = p1 i⊧HTf⇒g
    proof : h ⊧C (reduct f t) → h ⊧C (reduct g t)
    proof h⊧Cf^t = h⊧Cg^t
      where
        -- as h is a classical model of the reduct of f
        -- i is a model of f
        i⊧HTf = reduct-to-ht h⊧Cf^t
        -- the i is a model of g
        i⊧HTg = i⊧HTf→i⊧HTg i⊧HTf
        -- and thus h is a model of the reduct of g
        h⊧Cg^t = ht-to-reduct i⊧HTg

-- relationship equilibrium models and stable model ----------------------------
-- if i is an equilibrium model of f it is also a stable model
eq-to-sm : {i : IPC} → {f : F} → (i ⊧EQ f) → i ⊧SM f
eq-to-sm {i} {f} (i⊧HTf , i-min-h) = i⊧Cf^i , i-min-c
  where
    -- 1) i is a classical model of the reduct of f
    i⊧Cf^i = ht-to-reduct i⊧HTf
    -- 2) i is the minimal model of the reduct of f
    i-min-c : (j : IPC) → j ⊆ i → j ⊧C (reduct f i) → j ≡ i
    i-min-c j j⊆i j⊧Cf^i =
      let
        -- as j is a classical model of the reduct of f
        -- it (i.e. the total ht interpretation) is also a ht model of f
        j⊧HTf = reduct-to-ht j⊧Cf^i
      in
        -- but we know that i is minimal in the here component for f
        i-min-h j j⊆i j⊧HTf

sm-to-eq : {i : IPC} → {f : F} → (i ⊧SM f) → i ⊧EQ f
sm-to-eq {i} {f} (i⊧Cf^i , i-min-c) = i⊧HTf , i-min-h
  where
    -- 1) i is a ht model of f
    i⊧HTf = reduct-to-ht i⊧Cf^i
    -- 2) i is minimal in the here component for f
    i-min-h : (j : IPC) → (p : j ⊆ i) → (IHT j i p) ⊧HT f → j ≡ i
    i-min-h j j⊆i ji⊧HTf =
      let
        -- as <j,i> is a ht model of f, we also have that j is a classical model
        -- of the reduct of f with respect to i
        j⊧Cf^i = ht-to-reduct ji⊧HTf
      in
        -- but we know that i is the minimal classical model of this reduct
        i-min-c j j⊆i j⊧Cf^i
