module HT where

open import Agda.Builtin.Equality
open import Data.Nat
open import Data.Bool renaming (Bool to 𝔹 ; _∧_ to _∧𝔹_ ; _∨_ to _∨𝔹_ ; not to ¬𝔹)
open import Data.List using (List ; _∷_ ; [])
open import Data.Empty renaming (⊥ to Ø)
open import Data.Sum.Base using (_⊎_) renaming (inj₁ to inl ; inj₂ to inr)
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

-- theories --------------------------------------------------------------------
Th : Set
Th = List F
-- element operator for theories
infix 15 _∈_

_∈_ : F → Th → Set
f ∈ [] = Ø
f ∈ (g ∷ gs) = (f ≡ g) ⊎ (f ∈ gs)

-- classical model relation-----------------------------------------------------
infix 20 _⊧C_

_⊧C_ : IPC → Th → Set
m ⊧C th = (f : F) → f ∈ th → evalC m f ≡ true

-- here-and-there model relation -----------------------------------------------
infix 22 _⊧HT_

_⊧HT_ : IPHT → Th → Set
m ⊧HT th = (f : F) → f ∈ th -> evalHT m f ≡ true

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

-- generalisation to models
⊧-total-ht-to-c : (t : IPC) → (th : Th) → ((THT t) ⊧HT th) → (t ⊧C th)
⊧-total-ht-to-c t th p = λ (f : F) (e : f ∈ th) → total-ht-to-c t f true (p f e)

⊧-total-c-to-ht : (t : IPC) → (th : Th) → (t ⊧C th) → ((THT t) ⊧HT th)
⊧-total-c-to-ht t th p = λ (f : F) (e : f ∈ th) → total-c-to-ht t f true (p f e)

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

⊧-here-to-there : (i : IPHT) → (th : Th) → (i ⊧HT th) → ((THT (pt i)) ⊧HT th)
⊧-here-to-there i th p = λ (f : F) (e : f ∈ th) → here-to-there i f (p f e)

-- rephrasing of property 1 for countermodels
-- <T,T> not⊧HT f implies <H,T> not⊧HT f
contra : (a b : 𝔹) → (a ≡ true → b ≡ true) → b ≡ false → a ≡ false
contra false b i f = refl
contra true false i f = symm (i refl)

inc-neg : (h : IPC) → (t : IPC) → ((a : Var) → (h a ≡ true) → (t a ≡ true)) → (a : Var) → (t a ≡ false) → (h a ≡ false)
inc-neg h t p a f = contra (h a) (t a) (p a) f

counter-there-to-here : (t : IPC) → (f : F) → ((evalHT (THT t) f) ≡ false) → ((h : IPC) → (p : (a : Var) → (h a ≡ true) → (t a ≡ true)) → ((evalHT (IHT h t p) f) ≡ false))
counter-there-to-here t ⊥ c h p = refl
counter-there-to-here t (V a) c h p = inc-neg h t p a c
counter-there-to-here t (f ∧ g) c h p with ∧𝔹-to-⊎ c
... | inl a = ⊎-to-∧𝔹 (inl (counter-there-to-here t f a h p))
... | inr a = ⊎-to-∧𝔹 (inr (counter-there-to-here t g a h p))
counter-there-to-here t (f ∨ g) c h p =
                      ×-to-∨𝔹 (counter-there-to-here t f (p1 (∨𝔹-to-× c)) h p ,
                               counter-there-to-here t g (p2 (∨𝔹-to-× c)) h p)
counter-there-to-here t (f ⇒ g) c h p = ⊎-to-∧𝔹 (inr (total-ht-to-c t (f ⇒ g) false c))

-- satisfaction of negated formulas only depends on the "there"
-- <H,T> ⊧HT ¬ f iff T ⊧C ¬ f
-- property 2
neg-ht-to-c : (i : IPHT) → (f : F) → ((evalHT i (¬ f)) ≡ true) → ((evalC (pt i) (¬ f)) ≡ true)
neg-ht-to-c i@(IHT h t p) f s = total-ht-to-c t (¬ f) true (here-to-there i (¬ f) s)

neg-c-to-ht : (i : IPHT) → (f : F) → ((evalC (pt i) (¬ f)) ≡ true) → ((evalHT i (¬ f)) ≡ true)
-- evalC t (¬ f) ≡ true -> evalHT (THT t) (¬ f) ≡ true with total-c-to-ht
-- evalHT (THT t) (¬ f) ≡ true -> evalHT (THT t) f ≡ false with ?
-- evalHT (THT t) f ≡ false -> evalHT (IHT h t p) f ≡ false with counter-there-to-here
-- evalHT (IHT h t p) f ≡ false -> evalHT (IHT h t p) (¬ f) ≡ true with ?
neg-c-to-ht i@(IHT h t p) f s = {!!}
