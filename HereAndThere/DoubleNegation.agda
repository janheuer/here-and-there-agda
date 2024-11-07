module HereAndThere.DoubleNegation where

open import HereAndThere
open import HereAndThere.NestedLogicPrograms
open import Formula.LogicPrograms
open import Formula.LogicPrograms.Nested
open import Formula.LogicPrograms.DoubleNegation

-- removal of double negation --------------------------------------------------
r2¬-eq-r : (ϕ : R2¬) → Σ R (λ ψ → ValidHT ((r2¬f ϕ) ⇔ (rf ψ)))
r2¬-eq-r ϕ = {!!}

lp2¬-eq-lp : (Γ : LP2¬) → Σ LP (λ Π → ValidHT (Th2F (lp2¬t Γ) ⇔ Th2F (lpt Π)))
lp2¬-eq-lp Γ = {!!}
