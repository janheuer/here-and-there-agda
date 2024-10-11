module Formula.Decidable where

open import Relation.Nullary using (Dec ; yes ; no) public
open import Data.Nat using (zero ; suc)

open import Formula.Base

-- equality of formulas is decidable -------------------------------------------
-- equality of natural numbers is decidable
0≢suc : {n : ℕ} → zero ≡ suc n → Ø
0≢suc ()

suc≢0 : {n : ℕ} → suc n ≡ zero → Ø
suc≢0 ()

suc≢ : {n m : ℕ} → (n ≡ m → Ø) → suc n ≡ suc m → Ø
suc≢ n≢m refl = n≢m refl

_≡ℕ?_ : (n m : ℕ) → Dec (n ≡ m)
zero ≡ℕ? zero = yes refl
zero ≡ℕ? suc m = no 0≢suc
suc n ≡ℕ? zero = no suc≢0
suc n ≡ℕ? suc m with n ≡ℕ? m
... | yes refl = yes refl
... | no  n≢m  = no (suc≢ n≢m)

-- equality of variables is decidable
X≢ : {n m : ℕ} → (n ≡ m → Ø) → X n ≡ X m → Ø
X≢ n≢m refl = n≢m refl

_≡Var?_ : (a b : Var) → Dec (a ≡ b)
X n ≡Var? X m with n ≡ℕ? m
... | yes refl = yes refl
... | no  n≢m  = no (X≢ n≢m)

-- formulas of different structure are not equal
⊥≢V : {a : Var} → ⊥ ≡ (V a) → Ø
⊥≢V ()

⊥≢∧ : {f g : F} → ⊥ ≡ (f ∧ g) → Ø
⊥≢∧ ()

⊥≢∨ : {f g : F} → ⊥ ≡ (f ∨ g) → Ø
⊥≢∨ ()

⊥≢⇒ : {f g : F} → ⊥ ≡ (f ⇒ g) → Ø
⊥≢⇒ ()

V≢⊥ : {a : Var} → (V a) ≡ ⊥ → Ø
V≢⊥ ()

V≢∧ : {a : Var} → {f g : F} → V a ≡ f ∧ g → Ø
V≢∧ ()

V≢∨ : {a : Var} → {f g : F} → V a ≡ f ∨ g → Ø
V≢∨ ()

V≢⇒ : {a : Var} → {f g : F} → V a ≡ f ⇒ g → Ø
V≢⇒ ()

∧≢⊥ : {f g : F} → f ∧ g ≡ ⊥ → Ø
∧≢⊥ ()

∧≢V : {f g : F} → {a : Var} → f ∧ g ≡ V a → Ø
∧≢V ()

∧≢∨ : {f g h k : F} → f ∧ g ≡ h ∨ k → Ø
∧≢∨ ()

∧≢⇒ : {f g h k : F} → f ∧ g ≡ h ⇒ k → Ø
∧≢⇒ ()

∨≢⊥ : {f g : F} → f ∨ g ≡ ⊥ → Ø
∨≢⊥ ()

∨≢V : {f g : F} → {a : Var} → f ∨ g ≡ V a → Ø
∨≢V ()

∨≢∧ : {f g h k : F} → f ∨ g ≡ h ∧ k → Ø
∨≢∧ ()

∨≢⇒ : {f g h k : F} → f ∨ g ≡ h ⇒ k → Ø
∨≢⇒ ()

⇒≢⊥ : {f g : F} → f ⇒ g ≡ ⊥ → Ø
⇒≢⊥ ()

⇒≢V : {f g : F} → {a : Var} → f ⇒ g ≡ V a → Ø
⇒≢V ()

⇒≢∨ : {f g h k : F} → f ⇒ g ≡ h ∨ k → Ø
⇒≢∨ ()

⇒≢∧ : {f g h k : F} → f ⇒ g ≡ h ∧ k → Ø
⇒≢∧ ()

-- constructors of F preserve inequality (in each component)
V≢ : {a b : Var} → ((a ≡ b) → Ø) → V a ≡ V b → Ø
V≢ a≢b refl = a≢b refl

∧l≢ : {f g h k : F} → ((f ≡ h) → Ø) → f ∧ g ≡ h ∧ k → Ø
∧l≢ f≢h refl = f≢h refl

∧r≢ : {f g h k : F} → ((g ≡ k) → Ø) → f ∧ g ≡ h ∧ k → Ø
∧r≢ g≢k refl = g≢k refl

∨l≢ : {f g h k : F} → ((f ≡ h) → Ø) → f ∨ g ≡ h ∨ k → Ø
∨l≢ f≢h refl = f≢h refl

∨r≢ : {f g h k : F} → ((g ≡ k) → Ø) → f ∨ g ≡ h ∨ k → Ø
∨r≢ g≢k refl = g≢k refl

⇒l≢ : {f g h k : F} → ((f ≡ h) → Ø) → f ⇒ g ≡ h ⇒ k → Ø
⇒l≢ f≢h refl = f≢h refl

⇒r≢ : {f g h k : F} → ((g ≡ k) → Ø) → f ⇒ g ≡ h ⇒ k → Ø
⇒r≢ g≢k refl = g≢k refl

-- decidability on F
_≡F?_ : (f g : F) → Dec (f ≡ g)
-- formulas with same structure
⊥       ≡F? ⊥             = yes refl
V a     ≡F? V b with a ≡Var? b
... | yes refl            = yes refl
... | no a≢b              = no (V≢ a≢b)
(f ∧ g) ≡F? (h ∧ k) with f ≡F? h | g ≡F? k
... | yes refl | yes refl = yes refl
... | yes refl | no  g≢k  = no (∧r≢ g≢k)
... | no f≢h   | _        = no (∧l≢ f≢h)
(f ∨ g) ≡F? (h ∨ k) with f ≡F? h | g ≡F? k
... | yes refl | yes refl = yes refl
... | yes refl | no  g≢k  = no (∨r≢ g≢k)
... | no f≢h   | _        = no (∨l≢ f≢h)
(f ⇒ g) ≡F? (h ⇒ k) with f ≡F? h | g ≡F? k
... | yes refl | yes refl = yes refl
... | yes refl | no  g≢k  = no (⇒r≢ g≢k)
... | no f≢h   | _        = no (⇒l≢ f≢h)
-- formulas with different structure
⊥       ≡F? V _           = no ⊥≢V
⊥       ≡F? (_ ∧ _)       = no ⊥≢∧
⊥       ≡F? (_ ∨ _)       = no ⊥≢∨
⊥       ≡F? (_ ⇒ _)       = no ⊥≢⇒
V _     ≡F? ⊥             = no V≢⊥
V _     ≡F? (_ ∧ _)       = no V≢∧
V _     ≡F? (_ ∨ _)       = no V≢∨
V _     ≡F? (_ ⇒ _)       = no V≢⇒
(_ ∧ _) ≡F? ⊥             = no ∧≢⊥
(_ ∧ _) ≡F? V _           = no ∧≢V
(_ ∧ _) ≡F? (_ ∨ _)       = no ∧≢∨
(_ ∧ _) ≡F? (_ ⇒ _)       = no ∧≢⇒
(_ ∨ _) ≡F? ⊥             = no ∨≢⊥
(_ ∨ _) ≡F? V _           = no ∨≢V
(_ ∨ _) ≡F? (_ ∧ _)       = no ∨≢∧
(_ ∨ _) ≡F? (_ ⇒ _)       = no ∨≢⇒
(_ ⇒ _) ≡F? ⊥             = no ⇒≢⊥
(_ ⇒ _) ≡F? V _           = no ⇒≢V
(_ ⇒ _) ≡F? (_ ∧ _)       = no ⇒≢∧
(_ ⇒ _) ≡F? (_ ∨ _)       = no ⇒≢∨
