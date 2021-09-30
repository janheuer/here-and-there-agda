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
