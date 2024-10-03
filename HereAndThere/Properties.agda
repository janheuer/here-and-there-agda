module HereAndThere.Properties where

open import HereAndThere.Base

-- total here-and-there interpretations collapse to classical logic ------------
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
total-c-to-ht {t} {f ⇒ g} s =
  (λ t⊧HTf → total-c-to-ht (s (total-ht-to-c t⊧HTf))) , s

-- truth in the "here" implies true in the "there" -----------------------------
-- <H,T> ⊧HT f implies <T,T> ⊧HT f
-- (property 1)
here-to-there : {i : IPHT} → {f : F} → i ⊧HT f → (THT (pt i)) ⊧HT f
here-to-there {IHT h t p} {V a} s = p a s
here-to-there {IHT h t p} {f ∧ g} (sf , sg) = here-to-there sf ,
                                              here-to-there sg
here-to-there {IHT h t p} {f ∨ g} (inl sf) = inl (here-to-there sf)
here-to-there {IHT h t p} {f ∨ g} (inr sg) = inr (here-to-there sg)
here-to-there {IHT h t p} {f ⇒ g} (_ , st) = total-c-to-ht st

-- <H,T> ⊧HT f implies T ⊧C f
ht-to-c : {i : IPHT} → {f : F} → i ⊧HT f → (pt i) ⊧C f
ht-to-c {i} {f} s = total-ht-to-c (here-to-there s)

-- rephrasing of property 1 for countermodels
-- <T,T> ⊭HT f implies <H,T> ⊭HT f
counter-there-to-here : {i : IPHT} → {f : F} → ((THT (pt i)) ⊧HT f → Ø) →
                        i ⊧HT f → Ø
counter-there-to-here {i} {f} t⊭HTf i⊧HTf = t⊭HTf (here-to-there i⊧HTf)

-- negation in HT only depends on the "there" ----------------------------------
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

-- HT is three valued ----------------------------------------------------------
-- for any interpretation <H,T> and formula f either:
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
  inr (inl ((λ (_ , i⊧HTg) → i⊭HTg i⊧HTg) , (ht-to-c i⊧HTf , t⊧Cg)))
... | inl i⊧HTf | inr (inr t⊭Cg) =
  inr (inr (λ (_ , t⊧Cg) → t⊭Cg t⊧Cg))
... | inr (inl (i⊭HTf , t⊧Cf)) | inl i⊧HTg =
  inr (inl ((λ (i⊧HTf , _) → i⊭HTf i⊧HTf) , (t⊧Cf , ht-to-c i⊧HTg)))
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
  inr (inl ([ i⊭HTf , (λ i⊧HTg → t⊭Cg (ht-to-c i⊧HTg)) ] , inl t⊧Cf))
... | inr (inr t⊭Cf) | inl i⊧HTg =
  inl (inr i⊧HTg)
... | inr (inr t⊭Cf) | inr (inl (i⊭HTg , t⊧Cg)) =
  inr (inl ([ (λ i⊧HTf → t⊭Cf (ht-to-c i⊧HTf)) , i⊭HTg ] , inr t⊧Cg))
... | inr (inr t⊭Cf) | inr (inr t⊭Cg) =
  inr (inr [ t⊭Cf , t⊭Cg ])
3val (f ⇒ g) i@(IHT h t p) with 3val f i | 3val g i
... | inl i⊧HTf | inl i⊧HTg =
  inl ((λ _ → i⊧HTg) , (λ _ → ht-to-c i⊧HTg))
... | inl i⊧HTf | inr (inl (i⊭HTg , t⊧Cg)) =
  inr (inl ((λ (i⊧HTf⇒g , _) → i⊭HTg (i⊧HTf⇒g i⊧HTf)) , (λ _ → t⊧Cg)))
... | inl i⊧HTf | inr (inr t⊭Cg) =
  inr (inr (λ t⊧Cf⇒g → t⊭Cg (t⊧Cf⇒g (ht-to-c i⊧HTf))))
... | inr (inl (i⊭HTf , t⊧Cf)) | inl i⊧HTg =
  inl ((λ _ → i⊧HTg) , (λ _ → ht-to-c i⊧HTg))
... | inr (inl (i⊭HTf , t⊧Cf)) | inr (inl (i⊭HTg , t⊧Cg)) =
  inl ((λ i⊧HTf → Ø-elim (i⊭HTf i⊧HTf)) , (λ _ → t⊧Cg))
... | inr (inl (i⊭HTf , t⊧Cf)) | inr (inr t⊭Cg) =
  inr (inr (λ t⊧Cf⇒g → t⊭Cg (t⊧Cf⇒g t⊧Cf)))
... | inr (inr t⊭Cf) | _ =
  inl ((λ i⊧HTf → Ø-elim (t⊭Cf (ht-to-c i⊧HTf))) ,
       (λ t⊧Cf → Ø-elim (t⊭Cf t⊧Cf)))
