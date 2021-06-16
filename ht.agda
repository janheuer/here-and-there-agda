module HT where

open import Agda.Builtin.Equality
open import Data.Nat
open import Data.Bool renaming (Bool to 𝔹 ; _∧_ to _∧𝔹_ ; _∨_ to _∨𝔹_ ; not to ¬𝔹)
open import Data.List using (List ; _∷_ ; [])
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim)
open import Data.Sum.Base using (_⊎_ ; [_,_]) renaming (inj₁ to inl ; inj₂ to inr)
open import Data.Product using (_×_ ; _,_) renaming (proj₁ to p1 ; proj₂ to p2)

-- boolean implication
_⇒𝔹_ : 𝔹 → 𝔹 → 𝔹
f ⇒𝔹 g = (¬𝔹 f) ∨𝔹 g

symm : {A : Set} → {x y : A} → x ≡ y → y ≡ x
symm refl = refl

-- propositional signature -----------------------------------------------------
data Var : Set where
  X : ℕ → Var

-- formulas --------------------------------------------------------------------
infixr 12 _⇒_
infixr 10 _∧_
infixr  8 _∨_

data F : Set where
  ⊥   : F
  V   : Var → F
  _∧_ : F → F → F
  _∨_ : F → F → F
  _⇒_ : F → F → F
-- formula abbreviations
¬ : F → F
¬ f = f ⇒ ⊥

⊤ : F
⊤ = ⊥ ⇒ ⊥

_⇔_ : F → F → F
f ⇔ g = (f ⇒ g) ∧ (g ⇒ f)

-- theories
Th : Set
Th = List F
-- element operator for theories
infix 15 _∈_

_∈_ : F → Th → Set
f ∈ [] = Ø
f ∈ (g ∷ gs) = (f ≡ g) ⊎ (f ∈ gs)

All : (F → Set) → Th → Set
All P th = (f : F) → f ∈ th → P f
-- classical interpretations ---------------------------------------------------
IPC : Set
IPC = Var → 𝔹

-- satisfiability of formulas in classical logic -------------------------------
evalC : IPC → F → 𝔹
evalC _ ⊥ = false
evalC i (V a) = i a
evalC i (f ∧ g) = (evalC i f) ∧𝔹 (evalC i g)
evalC i (f ∨ g) = (evalC i f) ∨𝔹 (evalC i g)
evalC i (f ⇒ g) = (evalC i f) ⇒𝔹 (evalC i g)

infix 20 _⊧Ce_

_⊧Ce_ : IPC → F → Set
i ⊧Ce f = evalC i f ≡ true

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

-- some helper functions used in the following proofs --------------------------
×-to-∧𝔹 : {a b : 𝔹} → ((a ≡ true) × (b ≡ true)) → ((a ∧𝔹 b) ≡ true)
×-to-∧𝔹 {true} {true} _ = refl

∧𝔹-to-× : {a b : 𝔹} → ((a ∧𝔹 b) ≡ true) → ((a ≡ true) × (b ≡ true))
∧𝔹-to-× {true} {true} _ = refl , refl

⊎-to-∨𝔹 : {a b : 𝔹} → ((a ≡ true) ⊎ (b ≡ true)) → ((a ∨𝔹 b) ≡ true)
⊎-to-∨𝔹 {true} (inl _) = refl
⊎-to-∨𝔹 {false} {true} (inr _) = refl
⊎-to-∨𝔹 {true} {true} (inr _) = refl

∨𝔹-to-⊎ : {a b : 𝔹} → ((a ∨𝔹 b) ≡ true) → ((a ≡ true) ⊎ (b ≡ true))
∨𝔹-to-⊎ {false} p = inr p
∨𝔹-to-⊎ {true} p = inl p

⇒𝔹-to-⊎ : {a b : 𝔹} → ((a ⇒𝔹 b) ≡ true) → ((a ≡ false) ⊎ (b ≡ true))
⇒𝔹-to-⊎ {false} p = inl refl
⇒𝔹-to-⊎ {true} {true} p = inr refl

⊎-to-∧𝔹 : {a b : 𝔹} → ((a ≡ false) ⊎ (b ≡ false)) → ((a ∧𝔹 b) ≡ false)
⊎-to-∧𝔹 {false} (inl x) = refl
⊎-to-∧𝔹 {false} {false} (inr y) = refl
⊎-to-∧𝔹 {true} {false} (inr y) = refl

∧𝔹-to-⊎ : {a b : 𝔹} → ((a ∧𝔹 b) ≡ false) → ((a ≡ false) ⊎ (b ≡ false))
∧𝔹-to-⊎ {false} p = inl refl
∧𝔹-to-⊎ {true} {false} p = inr refl

×-to-∨𝔹 : {a b : 𝔹} → ((a ≡ false) × (b ≡ false)) → ((a ∨𝔹 b) ≡ false)
×-to-∨𝔹 {false} {false} p = refl

∨𝔹-to-× : {a b : 𝔹} → ((a ∨𝔹 b) ≡ false) → ((a ≡ false) × (b ≡ false))
∨𝔹-to-× {false} {false} p = refl , refl

¬𝔹-f-t : {b : 𝔹} → (b ≡ false) → ((¬𝔹 b) ≡ true)
¬𝔹-f-t {false} p = refl

¬𝔹-t-f : {b : 𝔹} → (b ≡ true) → ((¬𝔹 b) ≡ false)
¬𝔹-t-f {true} p = refl

remove-¬𝔹 : {a b : 𝔹} → ((¬𝔹 (¬𝔹 a)) ≡ b) → (a ≡ b)
remove-¬𝔹 {false} {false} p = refl
remove-¬𝔹 {true} {true} p = refl

→-to-⇒𝔹 : {a b : 𝔹} → (a ≡ true → b ≡ true) → a ⇒𝔹 b ≡ true
→-to-⇒𝔹 {false} p = refl
→-to-⇒𝔹 {true} {b} p = p refl

⇒𝔹-to-→ : {a b : 𝔹} → (a ⇒𝔹 b ≡ true) → a ≡ true → b ≡ true
⇒𝔹-to-→ {false} {false} p = λ x → x
⇒𝔹-to-→ {false} {true} p = λ x → refl
⇒𝔹-to-→ {true} {true} p = λ x → refl

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
contra : (a b : 𝔹) → (a ≡ true → b ≡ true) → b ≡ false → a ≡ false
contra false b i f = refl
contra true false i f = symm (i refl)

counter-there-to-here : (t : IPC) → (f : F) → ((evalHT (THT t) f) ≡ false) → ((h : IPC) → (p : (a : Var) → (h a ≡ true) → (t a ≡ true)) → ((evalHT (IHT h t p) f) ≡ false))
counter-there-to-here t f c h p = contra (evalHT (IHT h t p) f) (evalHT (THT t) f) (here-to-there (IHT h t p) f) c

-- alternative model definitions -----------------------------------------------
_⊧C_ : IPC → F → Set
i ⊧C ⊥ = Ø
i ⊧C (V a) = i a ≡ true
i ⊧C (f ∧ g) = (i ⊧C f) × (i ⊧C g)
i ⊧C (f ∨ g) = (i ⊧C f) ⊎ (i ⊧C g)
i ⊧C (f ⇒ g) = (i ⊧C f) → (i ⊧C g)

_⊧HT_ : IPHT → F → Set
i ⊧HT ⊥ = Ø
(IHT h _ _) ⊧HT (V a) = h a ≡ true
i ⊧HT (f ∧ g) = (i ⊧HT f) × (i ⊧HT g)
i ⊧HT (f ∨ g) = (i ⊧HT f) ⊎ (i ⊧HT g)
i@(IHT _ t _) ⊧HT (f ⇒ g) = ((i ⊧HT f) → (i ⊧HT g)) × (t ⊧C (f ⇒ g))

-- equivalence proofs
⊧C-to-⊧Ce : {i : IPC} → {f : F} → i ⊧C f → i ⊧Ce f
⊧Ce-to-⊧C : {i : IPC} → {f : F} → i ⊧Ce f → i ⊧C f

⊧C-to-⊧Ce {i} {V a} s = s
⊧C-to-⊧Ce {i} {f ∧ g} (sf , sg) = ×-to-∧𝔹 (⊧C-to-⊧Ce sf , ⊧C-to-⊧Ce sg)
⊧C-to-⊧Ce {i} {f ∨ g} (inl sf) = ⊎-to-∨𝔹 (inl (⊧C-to-⊧Ce sf))
⊧C-to-⊧Ce {i} {f ∨ g} (inr sg) = ⊎-to-∨𝔹 (inr (⊧C-to-⊧Ce sg))
⊧C-to-⊧Ce {i} {f ⇒ g} s = →-to-⇒𝔹 (λ sef → ⊧C-to-⊧Ce (s (⊧Ce-to-⊧C sef)))

⊧Ce-to-⊧C {i} {V a} s = s
⊧Ce-to-⊧C {i} {f ∧ g} s =
  let
    (sf , sg) = ∧𝔹-to-× s
  in
    (⊧Ce-to-⊧C sf , ⊧Ce-to-⊧C sg)
⊧Ce-to-⊧C {i} {f ∨ g} s with ∨𝔹-to-⊎ s
... | inl sf = inl (⊧Ce-to-⊧C sf)
... | inr sg = inr (⊧Ce-to-⊧C sg)
⊧Ce-to-⊧C {i} {f ⇒ g} s = λ x → ⊧Ce-to-⊧C ((⇒𝔹-to-→ s) (⊧C-to-⊧Ce x))

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
neg-ht-to-c : (i : IPHT) → (f : F) → ((evalHT i (¬ f)) ≡ true) → ((evalC (pt i) (¬ f)) ≡ true)
neg-ht-to-c i@(IHT h t p) f s = total-ht-to-c t (¬ f) true (here-to-there i (¬ f) s)

neg-c-to-ht : (i : IPHT) → (f : F) → ((evalC (pt i) (¬ f)) ≡ true) → ((evalHT i (¬ f)) ≡ true)
-- evalC t (¬ f) ≡ true -> evalHT (THT t) (¬ f) ≡ true with total-c-to-ht
-- evalHT (THT t) (¬ f) ≡ true -> evalHT (THT t) f ≡ false with ?
-- evalHT (THT t) f ≡ false -> evalHT (IHT h t p) f ≡ false with counter-there-to-here
-- evalHT (IHT h t p) f ≡ false -> evalHT (IHT h t p) (¬ f) ≡ true with ?
neg-c-to-ht i@(IHT h t p) f s = {!!}
