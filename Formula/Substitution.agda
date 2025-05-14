module Formula.Substitution where

open import Agda.Builtin.Equality using (refl)
open import Relation.Nullary using (Dec ; yes ; no)

open import Formula.Base
open import Formula.Decidable

-- substitution ----------------------------------------------------------------
-- f [ j / g ] replaces all occurrences of g in f with j
_[_/_] : F → F → F → F
f       [ j /  g ] with f ≡F? g
-- 1) f ≡ g
f       [ j / .f ] | yes refl = j
-- 2) f ≢ g
-- 2A) if f is atomic we do nothing
⊥       [ j /  g ] | no _     = ⊥
(V a)   [ j /  g ] | no _     = V a
-- 2B) otherwise we substitute in the components of f
(h ∧ k) [ j /  g ] | no _     = h [ j / g ] ∧ k [ j / g ]
(h ∨ k) [ j /  g ] | no _     = h [ j / g ] ∨ k [ j / g ]
(h ⇒ k) [ j /  g ] | no _     = h [ j / g ] ⇒ k [ j / g ]
