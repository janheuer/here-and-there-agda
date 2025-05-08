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

isLiteralConjunction : F → Set
isLiteralConjunction (f ∧ g) = isLiteralConjunction f × isLiteralConjunction g
isLiteralConjunction f = isLiteral f

LiteralConjunction : Set
LiteralConjunction = Σ[ f ∈ F ] isLiteralConjunction f

isEmptyBody : F → Set
isEmptyBody (⊥ ⇒ ⊥) = Unit
isEmptyBody _ = Ø

EmptyBody : Set
EmptyBody = Σ[ f ∈ F ] isEmptyBody f

isBody : F → Set
isBody f = (isEmptyBody f) ⊎ (isLiteralConjunction f)

Body : Set
Body = Σ[ f ∈ F ] isBody f

isLiteralDisjunction : F → Set
isLiteralDisjunction (f ∨ g) = isLiteralDisjunction f × isLiteralDisjunction g
isLiteralDisjunction f = isLiteral f

LiteralDisjunction : Set
LiteralDisjunction = Σ[ f ∈ F ] isLiteralDisjunction f

isEmptyHead : F → Set
isEmptyHead ⊥ = Unit
isEmptyHead _ = Ø

EmptyHead : Set
EmptyHead = Σ[ f ∈ F ] isEmptyHead f

isHead : F → Set
isHead f = (isEmptyHead f) ⊎ (isLiteralDisjunction f)

Head : Set
Head = Σ[ f ∈ F ] isHead f

-- isFact : F → Set
-- isFact ((⊥ ⇒ ⊥) ⇒ f) = isLiteralDisjunction f
-- isFact _ = Ø

-- Fact : Set
-- Fact = Σ[ f ∈ F ] isFact f

-- isConstraint : F → Set
-- isConstraint (f ⇒ ⊥) = isLiteralDisjunction f
-- isConstraint _ = Ø

-- Constraint : Set
-- Constraint = Σ[ f ∈ F ] isConstraint f

-- isBasicRule : F → Set
-- isBasicRule (f ⇒ g) = isLiteralConjunction f × isLiteralDisjunction g
-- isBasicRule _ = Ø

-- BasicRule : Set
-- BasicRule = Σ[ f ∈ F ] isBasicRule f

-- isRule : F → Set
-- isRule f = (isFact f) ⊎ (isConstraint f) ⊎ (isBasicRule f)

-- Rule : Set
-- Rule = Σ[ f ∈ F ] isRule f

isRule : F → Set
isRule (b ⇒ h) = (isBody b) × (isHead h)
isRule _ = Ø

Rule : Set
Rule = Σ[ f ∈ F ] isRule f

isLogicProgram : Th → Set
isLogicProgram [] = Unit
isLogicProgram (f ∷ th) = (isRule f) × (isLogicProgram th)

LogicProgram : Set
LogicProgram = Σ[ t ∈ Th ] (isLogicProgram t)
