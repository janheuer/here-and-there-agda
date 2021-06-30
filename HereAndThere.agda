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
_⊆_ : IPC → IPC → Set
h ⊆ t = (a : Var) → h a ≡ true → t a ≡ true

data IPHT : Set where
  IHT : (h t : IPC) → h ⊆ t → IPHT
-- shorthand for total here-and-there interpretation
THT : IPC → IPHT
THT t = IHT t t (λ a p → p)
-- projections to extract the components of a ht interpretation
ph : IPHT → IPC
ph (IHT h t p) = h

pt : IPHT → IPC
pt (IHT h t p) = t

pi : (i : IPHT) → (ph i) ⊆ (pt i)
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

-- HT is three valued ----------------------------------------------------------
-- 2 : <H,T> ⊧HT f
-- 1 : <H,T> ⊭HT f and T ⊧C f
-- 0 :                 T ⊭C f
3val : (f : F) → (i : IPHT) → (i ⊧HT f) ⊎ (((i ⊧HT f) → Ø ) × ((pt i) ⊧C f)) ⊎ (((pt i) ⊧C f) → Ø)
3val ⊥ i = inr (inr (λ ()))
3val (V a) i@(IHT h t p) with h a
... | true  = inl refl
... | false with t a
...         | true  = inr (inl ((λ ()) , refl))
...         | false = inr (inr (λ ()))
3val (f ∧ g) i@(IHT h t p) with 3val f i | 3val g i
... | inl i⊧HTf | inl i⊧HTg = inl (i⊧HTf , i⊧HTg)
... | inl i⊧HTf | inr (inl (i⊭HTg , t⊧Cg)) =
  inr (inl ((λ (_ , i⊧HTg) → i⊭HTg i⊧HTg) , (here-to-c i⊧HTf , t⊧Cg)))
... | inl i⊧HTf | inr (inr t⊭Cg) = inr (inr (λ (_ , t⊧Cg) → t⊭Cg t⊧Cg))
... | inr (inl (i⊭HTf , t⊧Cf)) | inl i⊧HTg =
  inr (inl ((λ (i⊧HTf , _) → i⊭HTf i⊧HTf) , (t⊧Cf , here-to-c i⊧HTg)))
... | inr (inl (i⊭HTf , t⊧Cf)) | inr (inl (i⊭HTg , t⊧Cg)) =
  inr (inl ((λ (i⊧HTf , _) → i⊭HTf i⊧HTf) , (t⊧Cf , t⊧Cg)))
... | inr (inl (i⊭HTf , t⊧Cf)) | inr (inr t⊭Cg) = inr (inr (λ (_ , t⊧Cg) → t⊭Cg t⊧Cg))
... | inr (inr t⊭Cf) | _ = inr (inr (λ (t⊧Cf , _) → t⊭Cf t⊧Cf))
3val (f ∨ g) i@(IHT h t p) with 3val f i | 3val g i
... | inl i⊧HTf | _ = inl (inl i⊧HTf)
... | inr (inl (i⊭HTf , t⊧Cf)) | inl i⊧HTg = inl (inr i⊧HTg)
... | inr (inl (i⊭HTf , t⊧Cf)) | inr (inl (i⊭HTg , t⊧Cg)) =
  inr (inl ([ i⊭HTf , i⊭HTg ] , inr t⊧Cg))
... | inr (inl (i⊭HTf , t⊧Cf)) | inr (inr t⊭Cg) =
  inr (inl ([ i⊭HTf , (λ i⊧HTg → t⊭Cg (here-to-c i⊧HTg)) ] , inl t⊧Cf))
... | inr (inr t⊭Cf) | inl i⊧HTg = inl (inr i⊧HTg)
... | inr (inr t⊭Cf) | inr (inl (i⊭HTg , t⊧Cg)) =
  inr (inl ([ (λ i⊧HTf → t⊭Cf (here-to-c i⊧HTf)) , i⊭HTg ] , inr t⊧Cg))
... | inr (inr t⊭Cf) | inr (inr t⊭Cg) = inr (inr [ t⊭Cf , t⊭Cg ])
3val (f ⇒ g) i@(IHT h t p) with 3val f i | 3val g i
... | inl i⊧HTf | inl i⊧HTg = inl ((λ _ → i⊧HTg) , (λ _ → here-to-c i⊧HTg))
... | inl i⊧HTf | inr (inl (i⊭HTg , t⊧Cg)) =
  inr (inl ((λ (i⊧HTf⇒g , _) → i⊭HTg (i⊧HTf⇒g i⊧HTf)) , (λ _ → t⊧Cg)))
... | inl i⊧HTf | inr (inr t⊭Cg) = inr (inr (λ t⊧Cf⇒g → t⊭Cg (t⊧Cf⇒g (here-to-c i⊧HTf))))
... | inr (inl (i⊭HTf , t⊧Cf)) | inl i⊧HTg = inl ((λ _ → i⊧HTg) , (λ _ → here-to-c i⊧HTg))
... | inr (inl (i⊭HTf , t⊧Cf)) | inr (inl (i⊭HTg , t⊧Cg)) =
  inl ((λ i⊧HTf → Ø-elim (i⊭HTf i⊧HTf)) , (λ _ → t⊧Cg))
... | inr (inl (i⊭HTf , t⊧Cf)) | inr (inr t⊭Cg) = inr (inr (λ t⊧Cf⇒g → t⊭Cg (t⊧Cf⇒g t⊧Cf)))
... | inr (inr t⊭Cf) | _ =
  inl ((λ i⊧HTf → Ø-elim (t⊭Cf (here-to-c i⊧HTf))) , (λ t⊧Cf → Ø-elim (t⊭Cf t⊧Cf)))

-- hosoi axiom -----------------------------------------------------------------
-- f ∨ (f ⇒ g) ∨ ¬g
hosoi : (f g : F) → ValidHT (f ∨ (f ⇒ g) ∨ (¬ g))
hosoi f g i@(IHT h t p) with 3val f i
... | inl i⊧HTf                  = inl i⊧HTf
... | inr (inr t⊭Cf)             = inr (inl ((λ i⊧HTf → Ø-elim (t⊭Cf (here-to-c i⊧HTf))) ,
                                             (λ t⊧Cf → Ø-elim (t⊭Cf t⊧Cf))))
... | inr (inl (i⊭HTf , t⊧Cf)) with 3val g i
...   | inl i⊧HTg                = inr (inl ((λ _ → i⊧HTg) , (λ _ → here-to-c i⊧HTg)))
...   | inr (inl (i⊭HTg , t⊧Cg)) = inr (inl ((λ i⊧HTf → Ø-elim (i⊭HTf i⊧HTf)) ,
                                             (λ _ → t⊧Cg)))
...   | inr (inr t⊭Cg)           = inr (inr ((λ i⊧HTg → t⊭Cg (here-to-c i⊧HTg)) , t⊭Cg))

-- removal of nested implication -----------------------------------------------
-- (f ⇒ g) ⇒ k is equivalent to (g ∨ ¬f) ⇒ k and k ∨ f ∨ ¬g
-- lemma 1
-- (f ⇒ g) ⇒ k implies (g ∨ ¬f) ⇒ k
rem-nested⇒1 : (f g k : F) → ValidHT (((f ⇒ g) ⇒ k) ⇒ ((g ∨ (¬ f)) ⇒ k))
rem-nested⇒1 f g k i@(IHT h t p) =
  ((λ i⊧HTf⇒g⇒k → ([ (λ i⊧HTg → (p1 i⊧HTf⇒g⇒k) ((λ _ → i⊧HTg) , (λ _ → here-to-c i⊧HTg))) ,
                     (λ i⊧HT¬f → (p1 i⊧HTf⇒g⇒k) ((λ i⊧HTf → Ø-elim ((p1 i⊧HT¬f) i⊧HTf)) ,
                                                 (λ t⊧Cf → Ø-elim ((p2 i⊧HT¬f) t⊧Cf)))) ] ,
                   [ (λ t⊧Cg → (p2 i⊧HTf⇒g⇒k) (λ _ → t⊧Cg)) ,
                     (λ t⊭Cf → (p2 i⊧HTf⇒g⇒k) (λ t⊧Cf → Ø-elim (t⊭Cf t⊧Cf))) ])) ,
   (λ t⊧Cf⇒g⇒k → [ (λ t⊧Cg → t⊧Cf⇒g⇒k (λ _ → t⊧Cg)) ,
                   (λ t⊭Cf → t⊧Cf⇒g⇒k (λ t⊧Cf → Ø-elim (t⊭Cf t⊧Cf))) ]))

-- (f ⇒ g) ⇒ k implies k ∨ f ∨ ¬g
rem-nested⇒2 : (f g k : F) → ValidHT (((f ⇒ g) ⇒ k) ⇒ (k ∨ f ∨ (¬ g)))
rem-nested⇒2 f g k i@(IHT h t p) with hosoi f g i
... | inl i⊧HTf = ((λ _ → inr (inl i⊧HTf)) , (λ _ → inr (inl (here-to-c i⊧HTf))))
... | inr (inl i⊧HTf⇒g) = ((λ i⊧HTf⇒g⇒k → inl ((p1 i⊧HTf⇒g⇒k) i⊧HTf⇒g)) ,
                           (λ t⊧Cf⇒g⇒k → inl (t⊧Cf⇒g⇒k (p2 i⊧HTf⇒g))))
... | inr (inr i⊧HT¬g) = ((λ _ → inr (inr i⊧HT¬g)) , (λ _ → inr (inr (p2 i⊧HT¬g))))

-- (f ⇒ g) ⇒ k implies (g ∨ ¬f) ⇒ k and k ∨ f ∨ ¬g
rem-nested⇒ : (f g k : F) → ValidHT (((f ⇒ g) ⇒ k) ⇒ (((g ∨ (¬ f)) ⇒ k) ∧ (k ∨ f ∨ (¬ g))))
rem-nested⇒ f g k i@(IHT h t p) =
  ((λ i⊧HTf⇒g⇒k → ((p1 (rem-nested⇒1 f g k i)) i⊧HTf⇒g⇒k ,
                   (p1 (rem-nested⇒2 f g k i)) i⊧HTf⇒g⇒k)) ,
   (λ t⊧Cf⇒g⇒k → ((p2 (rem-nested⇒1 f g k i)) t⊧Cf⇒g⇒k ,
                  (p2 (rem-nested⇒2 f g k i)) t⊧Cf⇒g⇒k)))

-- (g ∨ ¬f) ⇒ k and k ∨ f ∨ ¬g implies (f ⇒ g) ⇒ k
add-nested⇒ : (f g k : F) → ValidHT ((((g ∨ (¬ f)) ⇒ k) ∧ (k ∨ f ∨ (¬ g))) ⇒ ((f ⇒ g) ⇒ k))
add-nested⇒ f g k i@(IHT h t p) =
  ((λ where
      (i⊧HTg∨¬f⇒k , inl i⊧HTk)
        → ((λ _ → i⊧HTk) , (λ _ → here-to-c i⊧HTk))
      (i⊧HTg∨¬f⇒k , inr (inl i⊧HTf))
        → ((λ (i⊧HTf⇒g , _) → (p1 i⊧HTg∨¬f⇒k) (inl (i⊧HTf⇒g i⊧HTf))) ,
           (λ t⊧Cf⇒g → (p2 i⊧HTg∨¬f⇒k) (inl (t⊧Cf⇒g (here-to-c i⊧HTf)))))
      (i⊧HTg∨¬f⇒k , inr (inr i⊧HT¬g))
        → ((λ (i⊧HTf⇒g , t⊧Cf⇒g) → (p1 i⊧HTg∨¬f⇒k) (inr ((λ i⊧HTf → (p1 i⊧HT¬g) (i⊧HTf⇒g i⊧HTf)) ,
                                                         (λ t⊧Cf → (p2 i⊧HT¬g) (t⊧Cf⇒g t⊧Cf))))) ,
           (λ t⊧Cf⇒g → (p2 i⊧HTg∨¬f⇒k) (inr (λ t⊧Cf → (p2 i⊧HT¬g) (t⊧Cf⇒g t⊧Cf)))))) ,
   (λ where
      (t⊧Cg∨¬f⇒k , inl t⊧Ck)
        → (λ _ → t⊧Ck)
      (t⊧Cg∨¬f⇒k , inr (inl t⊧Cf))
        → (λ t⊧Cf⇒g → t⊧Cg∨¬f⇒k (inl (t⊧Cf⇒g t⊧Cf)))
      (t⊧Cg∨¬f⇒k , inr (inr t⊧C¬g))
        → (λ t⊧Cf⇒g → t⊧Cg∨¬f⇒k (inr (λ t⊧Cf → t⊧C¬g (t⊧Cf⇒g t⊧Cf))))))

-- disjunctions in ht can be rewritten with implication ------------------------
-- f ∨ g is equivalent to ((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)
-- f ∨ g implies ((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)
∨-to-⇒ : (f g : F) → ValidHT ((f ∨ g) ⇒ (((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)))
∨-to-⇒ f g i@(IHT h t p) =
  ([ (λ i⊧HTf → (((λ (i⊧HTf⇒g , _) → i⊧HTf⇒g i⊧HTf) , (λ t⊧Cf⇒g → t⊧Cf⇒g (here-to-c i⊧HTf))) ,
                 ((λ _ → i⊧HTf) , (λ _ → here-to-c i⊧HTf)))) ,
     (λ i⊧HTg → (((λ _ → i⊧HTg) , (λ _ → here-to-c i⊧HTg)) ,
                 ((λ (i⊧HTg⇒f , _) → i⊧HTg⇒f i⊧HTg) , (λ t⊧Cg⇒f → t⊧Cg⇒f (here-to-c i⊧HTg))))) ] ,
   [ (λ t⊧Cf → ((λ t⊧Cf⇒g → t⊧Cf⇒g t⊧Cf) , (λ _ → t⊧Cf))) ,
     (λ t⊧Cg → ((λ _ → t⊧Cg) , (λ t⊧Cg⇒f → t⊧Cg⇒f t⊧Cg))) ])

-- ((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f) implies f ∨ g
⇒-to-∨ : (f g : F) → ValidHT ((((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)) ⇒ (f ∨ g))
⇒-to-∨ f g i@(IHT h t p) with hosoi f g i
... | inl i⊧HTf = ((λ _ → inl i⊧HTf) , (λ _ → inl (here-to-c i⊧HTf)))
... | inr (inl i⊧HTf⇒g) =
  ((λ (i⊧HTf⇒g⇒g , _) → inr ((p1 i⊧HTf⇒g⇒g) i⊧HTf⇒g)) ,
   (λ (t⊧Cf⇒g⇒g , _) → inr (t⊧Cf⇒g⇒g (here-to-c {i} i⊧HTf⇒g))))
... | inr (inr i⊧HT¬g) =
  ((λ (_ , i⊧HTg⇒f⇒f) → inl ((p1 i⊧HTg⇒f⇒f) ((λ i⊧HTg → Ø-elim ((p1 i⊧HT¬g) i⊧HTg)) ,
                                              (λ t⊧Cg → Ø-elim ((p2 i⊧HT¬g) t⊧Cg))))) ,
   (λ (_ , t⊧Cg⇒f⇒f) → inl (t⊧Cg⇒f⇒f (λ t⊧Cg → Ø-elim ((p2 i⊧HT¬g) t⊧Cg)))))

-- de morgan -------------------------------------------------------------------
-- ¬(f ∧ g) is equivalent to ¬f ∨ ¬g
-- ¬(f ∧ g) implies ¬f ∨ ¬g
demorgan⇒ : (f g : F) → ValidHT ((¬ (f ∧ g)) ⇒ ((¬ f) ∨ (¬ g)))
demorgan⇒ f g i@(IHT h t p) with hosoi f g i
... | inl i⊧HTf =
  ((λ (i⊭HTf∧g , t⊭Cf∧g) → inr ((λ i⊧HTg → i⊭HTf∧g (i⊧HTf , i⊧HTg)) ,
                                (λ t⊧Cg → t⊭Cf∧g (here-to-c i⊧HTf , t⊧Cg)))) ,
   (λ t⊭Cf∧g → inr (λ t⊧Cg → t⊭Cf∧g (here-to-c i⊧HTf , t⊧Cg))))
... | inr (inl (i⊧HTf⇒g , t⊧Cf⇒g)) =
  ((λ (i⊭HTf∧g , t⊭Cf∧g) → inl ((λ i⊧HTf → i⊭HTf∧g (i⊧HTf , i⊧HTf⇒g i⊧HTf)) ,
                                (λ t⊧Cf → t⊭Cf∧g (t⊧Cf , t⊧Cf⇒g t⊧Cf)))) ,
   (λ t⊭Cf∧g → inl (λ t⊧Cf → t⊭Cf∧g (t⊧Cf , t⊧Cf⇒g t⊧Cf))))
... | inr (inr (i⊭HTg , t⊭Cg)) =
  ((λ _ → inr (i⊭HTg , t⊭Cg)) ,
   (λ _ → inr t⊭Cg))

-- ¬f ∨ ¬g implies ¬(f ∧ g)
demorgan⇐ : (f g : F) → ValidHT (((¬ f) ∨ (¬ g)) ⇒ (¬ (f ∧ g)))
demorgan⇐ f g i@(IHT h t p) =
  let
    i⊧HT¬f⇒¬f∧g = λ (i⊭HTf , t⊭Cf)  → ((λ (i⊧HTf , _) → i⊭HTf i⊧HTf) ,
                                        (λ (t⊧Cf , _) → t⊭Cf t⊧Cf))
    i⊧HT¬g⇒¬f∧g = λ (i⊭HTg , t⊭Cg)  → ((λ (_ , i⊧HTg) → i⊭HTg i⊧HTg) ,
                                        (λ (_ , t⊧Cg) → t⊭Cg t⊧Cg))
    t⊧C¬f⇒¬f∧g  = λ t⊭Cf (t⊧Cf , _) → t⊭Cf t⊧Cf
    t⊧C¬g⇒¬f∧g  = λ t⊭Cg (_ , t⊧Cg) → t⊭Cg t⊧Cg
  in
    ([ i⊧HT¬f⇒¬f∧g , i⊧HT¬g⇒¬f∧g ] , [ t⊧C¬f⇒¬f∧g , t⊧C¬g⇒¬f∧g ])
