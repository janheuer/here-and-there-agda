module Formula.LogicPrograms.Base where

open import Agda.Builtin.Unit renaming (⊤ to Unit) using ()
open import Data.Empty renaming (⊥ to Ø) using()
open import Data.Product using (_×_ ; Σ-syntax)
open import Data.List using (List ; [] ; _∷_)
open import Data.Sum using (_⊎_)

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

-- alternative definition of logic programs ------------------------------------
isLiteral : F → Set
isLiteral (V a) = Unit
isLiteral ((V a) ⇒ ⊥) = Unit
isLiteral _ = Ø

Literal : Set
Literal = Σ[ f ∈ F ] (isLiteral f)

isEmptyBody : F → Set
isEmptyBody (⊥ ⇒ ⊥) = Unit
isEmptyBody _ = Ø

EmptyBody : Set
EmptyBody = Σ[ f ∈ F ] (isEmptyBody f)

isEmptyHead : F → Set
isEmptyHead ⊥ = Unit
isEmptyHead _ = Ø

EmptyHead : Set
EmptyHead = Σ[ f ∈ F ] (isEmptyHead f)

isBody : F → Set
isBody (f ∧ g) = (isBody f) × (isBody g)
isBody f = isEmptyBody f ⊎ isLiteral f

Body : Set
Body = Σ[ f ∈ F ] (isBody f)

isHead : F → Set
isHead (f ∨ g) = (isHead f) × (isHead g)
isHead f = isEmptyHead f ⊎ isLiteral f

Head : Set
Head = Σ[ f ∈ F ] (isHead f)

isRule : F → Set
isRule (f ⇒ g) = (isBody f) × (isHead g)
isRule _ = Ø

Rule : Set
Rule = Σ[ f ∈ F ] (isRule f)

isLogicProgram : Th → Set
isLogicProgram [] = Unit
isLogicProgram (f ∷ th) = (isRule f) × (isLogicProgram th)

LogicProgram : Set
LogicProgram = Σ[ t ∈ Th ] (isLogicProgram t)
