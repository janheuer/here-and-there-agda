module Formula.LogicPrograms.Base where

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

record BE : Set where
  constructor be
  field
    bef : F
    bep : isBE bef

open BE public

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

record HE : Set where
  constructor he
  field
    hef : F
    hep : isHE hef

open HE public

-- rules
isR : F → Set
isR (b ⇒ h) = (isBE b) × (isHE h)
isR _       = Ø

record R : Set where
  constructor rr
  field
    rf : F
    rp : isR rf

open R public

-- logic programs
isLP : Th → Set
isLP [] = Unit
isLP (r ∷ rs) = (isR r) × (isLP rs)

record LP : Set where
  constructor lp
  field
    lpt : Th
    lpp : isLP lpt

open LP public
