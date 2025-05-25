module Classical.Base where

-- this module defines classical interpretations as well as the classical
-- satisfiability relation

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool renaming (Bool to 𝔹) using (true ; false)
open import Data.Empty renaming (⊥ to Ø) using ()
open import Data.Sum.Base using (_⊎_)
open import Data.Product using (_×_)

open import Formula public

-- classical interpretations ---------------------------------------------------
-- usually an interpretation is the set of atoms that are true
-- here we model it instead as a function from atoms to booleans
IPC : Set
IPC = Var → 𝔹

-- satisfiability of formulas in classical logic -------------------------------
_⊧C_ : IPC → F → Set
-- false is never satisfied
i ⊧C ⊥       = Ø
-- an atom is satisfied if it is true in the interpretation
i ⊧C (V a)   = i a ≡ true
-- a conjunction is satisfied if both components are satisfied
i ⊧C (f ∧ g) = (i ⊧C f) × (i ⊧C g)
-- a disjunction is satisfied if one of the components is satisfied
i ⊧C (f ∨ g) = (i ⊧C f) ⊎ (i ⊧C g)
-- an implication is satisfied if we can turn a proof of satisfaction of f
-- into a proof of satisfaction of g
i ⊧C (f ⇒ g) = (i ⊧C f) → (i ⊧C g)

ValidC : F → Set
-- a formula is valid if it is satisfied by every interpretation
ValidC f = (i : IPC) → i ⊧C f

_⊆_ : IPC → IPC → Set
-- h is a subset of t if everything true in h is also true in t
h ⊆ t = (a : Var) → h a ≡ true → t a ≡ true
