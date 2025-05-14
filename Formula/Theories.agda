module Formula.Theories where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty renaming (⊥ to Ø) using ()
open import Data.Sum using (_⊎_)
open import Data.List using (List ; [] ; _∷_)

open import Formula.Base

-- theories --------------------------------------------------------------------
-- we model theories as lists of formulas
Th : Set
Th = List F

-- converting a theory to formula
Th2F : Th → F
Th2F []       = ⊤
Th2F (f ∷ th) = f ∧ (Th2F th)

-- element operator for theories
infix 15 _∈_

_∈_ : F → Th → Set
f ∈ [] = Ø
f ∈ (g ∷ gs) = (f ≡ g) ⊎ (f ∈ gs)
