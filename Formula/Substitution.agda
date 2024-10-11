module Formula.Substitution where

open import Formula.Base
open import Formula.Decidable

-- substitution ----------------------------------------------------------------
-- f [ j / g ] replaces all occurrences of g in f with j
_[_/_] : F → F → F → F
f       [ j /  g ] with f ≡F? g
f       [ j / .f ] | yes refl = j
⊥       [ j /  g ] | no _     = ⊥
(V a)   [ j /  g ] | no _     = V a
(h ∧ k) [ j /  g ] | no _     = h [ j / g ] ∧ k [ j / g ]
(h ∨ k) [ j /  g ] | no _     = h [ j / g ] ∨ k [ j / g ]
(h ⇒ k) [ j /  g ] | no _     = h [ j / g ] ⇒ k [ j / g ]
