module HereAndThere.Properties where

open import Agda.Builtin.Equality using (refl)
open import Data.Bool renaming (Bool to 𝔹) using (true ; false)
open import Data.Product using (_×_ ; _,_) renaming (proj₁ to p1 ; proj₂ to p2)
open import Data.Sum renaming (inj₁ to inl ; inj₂ to inr) using (_⊎_ ; [_,_])
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim) using ()

open import HereAndThere.Base

-- total here-and-there interpretations collapse to classical logic ------------
-- i.e. <T,T> ⊧HT f iff T ⊧C f
-- ht satisfiability implies classical satisfiability
total-ht-to-c : {t : IPC} → {f : F} → ((THT t) ⊧HT f) → (t ⊧C f)
total-ht-to-c {t} {V a} ta≡true = ta≡true
total-ht-to-c {t} {f ∧ g} (⊧HTf , ⊧HTg) = total-ht-to-c ⊧HTf , total-ht-to-c ⊧HTg
total-ht-to-c {t} {f ∨ g} (inl ⊧HTf) = inl (total-ht-to-c ⊧HTf)
total-ht-to-c {t} {f ∨ g} (inr ⊧HTg) = inr (total-ht-to-c ⊧HTg)
total-ht-to-c {t} {f ⇒ g} (⊧HTf⇒g , ⊧Cf⇒g) = ⊧Cf⇒g

-- classical satisfiability implies ht satisfiability
total-c-to-ht : {t : IPC} → {f : F} → (t ⊧C f) → ((THT t) ⊧HT f)
total-c-to-ht {t} {V a} ta≡true = ta≡true
total-c-to-ht {t} {f ∧ g} (⊧Cf , ⊧Cg) = total-c-to-ht ⊧Cf , total-c-to-ht ⊧Cg
total-c-to-ht {t} {f ∨ g} (inl ⊧Cf) = inl (total-c-to-ht ⊧Cf)
total-c-to-ht {t} {f ∨ g} (inr ⊧Cg) = inr (total-c-to-ht ⊧Cg)
total-c-to-ht {t} {f ⇒ g} ⊧Cf⇒g = ⊧HTf⇒g , ⊧Cf⇒g
  where
    ⊧HTf⇒g : (THT t) ⊧HT f → (THT t) ⊧HT g
    ⊧HTf⇒g ⊧HTf =
      let
        ⊧Cf = total-ht-to-c ⊧HTf
      in
        total-c-to-ht (⊧Cf⇒g ⊧Cf)

-- truth in the "here" implies true in the "there" -----------------------------
-- <H,T> ⊧HT f implies <T,T> ⊧HT f
here-to-there : {i : IPHT} → {f : F} → i ⊧HT f → (THT (pt i)) ⊧HT f
here-to-there {IHT h t h⊆t} {V a} ha≡true = h⊆t a ha≡true
here-to-there {IHT h t _} {f ∧ g} (⊧f , ⊧g) = here-to-there ⊧f ,
                                              here-to-there ⊧g
here-to-there {IHT h t _} {f ∨ g} (inl ⊧f) = inl (here-to-there ⊧f)
here-to-there {IHT h t _} {f ∨ g} (inr ⊧g) = inr (here-to-there ⊧g)
here-to-there {IHT h t _} {f ⇒ g} (_ , ⊧Cf⇒g) = total-c-to-ht ⊧Cf⇒g

-- <H,T> ⊧HT f implies T ⊧C f
ht-to-c : {i : IPHT} → {f : F} → i ⊧HT f → (pt i) ⊧C f
ht-to-c {i} {f} i⊧f = total-ht-to-c (here-to-there i⊧f)

-- rephrasing of here-to-there for countermodels
-- <T,T> ⊭HT f implies <H,T> ⊭HT f
counter-there-to-here : {i : IPHT} → {f : F} → ((THT (pt i)) ⊧HT f → Ø) →
                        i ⊧HT f → Ø
counter-there-to-here {i} {f} t⊭HTf i⊧HTf = t⊭HTf (here-to-there i⊧HTf)

-- negation in HT only depends on the "there" ----------------------------------
-- <H,T> ⊧HT ¬f iff T ⊧C ¬f
neg-ht-to-c : {i : IPHT} → {f : F} → i ⊧HT (¬ f) → (pt i) ⊧C (¬ f)
neg-ht-to-c {i} {f} (⊧HT¬f , ⊧C¬f) = ⊧C¬f

neg-c-to-ht : {i : IPHT} → {f : F} → (pt i) ⊧C (¬ f) → i ⊧HT (¬ f)
neg-c-to-ht {i@(IHT h t _)} {f} t⊧C¬f = i⊧HT¬f , t⊧C¬f
  where
    t⊭HTf : ((THT t) ⊧HT f) → Ø
    t⊭HTf t⊧HTf = t⊧C¬f (total-ht-to-c t⊧HTf)
    i⊧HT¬f = counter-there-to-here {i} {f} t⊭HTf

-- if ¬f and f hold every formula holds ----------------------------------------
contraHT : {i : IPHT} → {f : F} → (i ⊧HT f → Ø) → i ⊧HT f → (g : F) → i ⊧HT g
contraHT {i@(IHT h t p)} {f} ⊭HTf ⊧HTf g = Ø-elim (⊭HTf ⊧HTf)

-- if ¬f holds then for every formula g, f ⇒ g holds ---------------------------
¬f-imp-f⇒* : {i : IPHT} → {f : F} → i ⊧HT (¬ f) → (g : F) → i ⊧HT (f ⇒ g)
¬f-imp-f⇒* {i@(IHT h t p)} {f} (⊭HTf , ⊭Cf) g = ⊧HTf⇒g , ⊧Cf⇒g
  where
    ⊧Cf⇒g : t ⊧C f → t ⊧C g
    ⊧Cf⇒g ⊧Cf = contraC ⊭Cf ⊧Cf g

    ⊧HTf⇒g : i ⊧HT f → i ⊧HT g
    ⊧HTf⇒g ⊧HTf = contraHT ⊭HTf ⊧HTf g

-- HT is three valued ----------------------------------------------------------
-- for any interpretation <H,T> and formula f either:
-- 2 :  <H,T> ⊧HT f
-- 1 :  <H,T> ⊭HT f and  T ⊧C f
-- 0 : (<H,T> ⊭HT f and) T ⊭C f
3val : (f : F) → (i : IPHT) → (i ⊧HT f) ⊎                         -- 2: inl
                              (((i ⊧HT f) → Ø) × ((pt i) ⊧C f)) ⊎ -- 1: inr inl
                              (((pt i) ⊧C f) → Ø)                 -- 0: inr inr
-- if f is ⊥ we can proof 0
3val ⊥ i = inr (inr (λ ()))
-- for an atom we check whether h satisfies the atom
3val (V a) i@(IHT h t p) with h a
-- if it does we have i ⊧HT V a, i.e., 2
... | true  = inl refl
-- otherwise we check whether t satisfied the atom
... | false with t a
-- if it does we have 1
...         | true  = inr (inl ((λ ()) , refl))
-- if it doesnt we can show 0
...         | false = inr (inr (λ ()))

-- for conjunction we have to split over the values of both f and g
3val (f ∧ g) i@(IHT h t p) with 3val f i | 3val g i
-- if both are 2 their conjunction is also 2
... | inl i⊧HTf | inl i⊧HTg =
  inl (i⊧HTf , i⊧HTg)
-- if one of them is 0 the conjunction is 0
-- all three cases here are shown in the same manner
... | inr (inr t⊭Cf) | _ =
  inr (inr (λ (t⊧Cf , _) → t⊭Cf t⊧Cf))
... | inl i⊧HTf | inr (inr t⊭Cg) =
  inr (inr (λ (_ , t⊧Cg) → t⊭Cg t⊧Cg))
... | inr (inl (i⊭HTf , t⊧Cf)) | inr (inr t⊭Cg) =
  inr (inr (λ (_ , t⊧Cg) → t⊭Cg t⊧Cg))
-- otherwise we will proof 1 for the conjunction
-- in all cases we already have the proof that f ∧ g holds classically, as
-- we either have the classical proofs directly or we convert the ht proofs
-- to classical proofs
-- for the ht part we need to show that a proof of f ∧ g leads to a
-- contradiction
-- we will always have a proof that either f or g does not hold in ht
-- combining this with the assumption that f/g holds leads to a contradiction
... | inl i⊧HTf | inr (inl (i⊭HTg , t⊧Cg)) =
  inr (inl ((λ (_ , i⊧HTg) → i⊭HTg i⊧HTg) , (ht-to-c i⊧HTf , t⊧Cg)))
... | inr (inl (i⊭HTf , t⊧Cf)) | inl i⊧HTg =
  inr (inl ((λ (i⊧HTf , _) → i⊭HTf i⊧HTf) , (t⊧Cf , ht-to-c i⊧HTg)))
... | inr (inl (i⊭HTf , t⊧Cf)) | inr (inl (i⊭HTg , t⊧Cg)) =
  inr (inl ((λ (i⊧HTf , _) → i⊭HTf i⊧HTf) , (t⊧Cf , t⊧Cg)))

-- for disjunction we follow the same pattern as disjunction but slightly
-- altered
3val (f ∨ g) i@(IHT h t p) with 3val f i | 3val g i
-- if one of f or g is 2 the disjunction is 2
... | inl i⊧HTf | _ =
  inl (inl i⊧HTf)
... | inr (inl (i⊭HTf , t⊧Cf)) | inl i⊧HTg =
  inl (inr i⊧HTg)
... | inr (inr t⊭Cf) | inl i⊧HTg =
  inl (inr i⊧HTg)
-- if both are 0 the disjunction is also 0
... | inr (inr t⊭Cf) | inr (inr t⊭Cg) =
  inr (inr [ t⊭Cf , t⊭Cg ])
-- otherwise the disjunction is 1
... | inr (inl (i⊭HTf , t⊧Cf)) | inr (inl (i⊭HTg , t⊧Cg)) =
  inr (inl ([ i⊭HTf , i⊭HTg ] , inr t⊧Cg))
... | inr (inl (i⊭HTf , t⊧Cf)) | inr (inr t⊭Cg) =
  inr (inl ([ i⊭HTf , (λ i⊧HTg → t⊭Cg (ht-to-c i⊧HTg)) ] , inl t⊧Cf))
... | inr (inr t⊭Cf) | inr (inl (i⊭HTg , t⊧Cg)) =
  inr (inl ([ (λ i⊧HTf → t⊭Cf (ht-to-c i⊧HTf)) , i⊭HTg ] , inr t⊧Cg))

-- again we follow the same structure
3val (f ⇒ g) i@(IHT h t p) with 3val f i | 3val g i
-- we get 2 for the implication if either:
-- A) f is 0
... | inr (inr t⊭Cf) | _ =
  inl ((λ i⊧HTf → contraHT (p1 (neg-c-to-ht t⊭Cf)) i⊧HTf g) ,
       (λ t⊧Cf → contraC t⊭Cf t⊧Cf g))
-- B) g is 2
... | inl i⊧HTf | inl i⊧HTg =
  inl ((λ _ → i⊧HTg) , (λ _ → ht-to-c i⊧HTg))
... | inr (inl (i⊭HTf , t⊧Cf)) | inl i⊧HTg =
  inl ((λ _ → i⊧HTg) , (λ _ → ht-to-c i⊧HTg))
-- C) both are 1 (technically both are the same value, but the cases 2/2 and 0/0
-- are already covered in A and B)
... | inr (inl (i⊭HTf , t⊧Cf)) | inr (inl (i⊭HTg , t⊧Cg)) =
  inl ((λ i⊧HTf → contraHT i⊭HTf i⊧HTf g) , (λ _ → t⊧Cg))

-- if f is 2 and g is 1 the implication is 1
-- i.e. it holds classically as g holds classically
-- and it does not hold in ht: if we assume it holds in ht we get a proof that
-- g holds in ht (as we have a proof that f holds in ht) which contradicts
-- g being 1
... | inl i⊧HTf | inr (inl (i⊭HTg , t⊧Cg)) =
  inr (inl ((λ (i⊧HTf⇒g , _) → i⊭HTg (i⊧HTf⇒g i⊧HTf)) , (λ _ → t⊧Cg)))

-- if g is 0 the implication is 0 as well
-- i.e. f⇒g does not hold classically
-- in both cases if f⇒g holds classically we get that g holds classically
-- as we know that f holds classically (this is given if f is 1, for f is 2
-- we convert that f holds in ht into a proof that f holds classically)
-- thus if f⇒g holds we have both that g holds classically and that it does not
... | inl i⊧HTf | inr (inr t⊭Cg) =
  inr (inr (λ t⊧Cf⇒g → t⊭Cg (t⊧Cf⇒g (ht-to-c i⊧HTf))))
... | inr (inl (i⊭HTf , t⊧Cf)) | inr (inr t⊭Cg) =
  inr (inr (λ t⊧Cf⇒g → t⊭Cg (t⊧Cf⇒g t⊧Cf)))

-- decidability of HT ----------------------------------------------------------
-- for any interpretation <H,T> and formula f either:
-- <H,T> ⊧ f or
-- <H,T> ⊭ f
dec-HT : (f : F) → (i : IPHT) →
         (i ⊧HT f) ⊎ ((i ⊧HT f) → Ø)
-- this is a simple consequence of the 3-valuedness of HT
dec-HT f i with 3val f i
... | inl i⊧HTf = inl i⊧HTf
... | inr (inl ( i⊭HTf , _ )) = inr i⊭HTf
... | inr (inr t⊭Cf) = inr i⊭HTf
  where
    i⊭HTf = λ i⊧HTf → t⊭Cf (ht-to-c i⊧HTf)

-- ⊤ is valid ------------------------------------------------------------------
validHT-⊤ : ValidHT ⊤
validHT-⊤ i = (λ ()) , validC-⊤ (pt i)
