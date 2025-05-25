module Formula.LogicPrograms.Base where

-- logic programs have rules of the form
-- b1 ∧ ... ∧ bn ⇒ h1 ∨ ... ∨ hm
-- where each bi is ⊤ or V a or ¬(V a)
-- and each hi is ⊥ or V a or ¬(V a)

open import Agda.Builtin.Unit renaming (⊤ to Unit) using ()
open import Data.Empty renaming (⊥ to Ø) using()
open import Data.Product using (_×_ ; Σ-syntax)
open import Data.List using (List ; [] ; _∷_)

open import Formula

-- definition of logic programs ------------------------------------------------
-- body expressions
isBE : F → Set
-- empty conjunction
isBE (⊥ ⇒ ⊥)     = Unit
-- literals
isBE (V a)       = Unit
isBE ((V a) ⇒ ⊥) = Unit
-- conjunction of BE
isBE (f ∧ g)     = (isBE f) × (isBE g)
isBE ⊥           = Ø
isBE (f ∨ g)     = Ø
isBE (f ⇒ g)     = Ø

BE : Set
BE = Σ[ f ∈ F ] (isBE f)

-- head expressions
isHE : F → Set
-- empty disjunction
isHE ⊥           = Unit
-- literals
isHE (V a)       = Unit
isHE ((V a) ⇒ ⊥) = Unit
-- disjunction of HE
isHE (f ∨ g)     = (isHE f) × (isHE g)
isHE (f ∧ g)     = Ø
isHE (f ⇒ g)     = Ø

HE : Set
HE = Σ[ f ∈ F ] (isHE f)

-- rules
isR : F → Set
isR (b ⇒ h) = (isBE b) × (isHE h)
isR _       = Ø

R : Set
R = Σ[ f ∈ F ] (isR f)

-- logic programs
isLP : Th → Set
isLP [] = Unit
isLP (r ∷ rs) = (isR r) × (isLP rs)

LP : Set
LP = Σ[ t ∈ Th ] (isLP t)
