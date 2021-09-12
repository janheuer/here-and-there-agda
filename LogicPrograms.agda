module LogicPrograms where

open import Agda.Builtin.Equality
open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim)
open import Data.Sum.Base using (_⊎_ ; [_,_]) renaming (inj₁ to inl ; inj₂ to inr)
open import Data.Product using (_×_ ; _,_) renaming (proj₁ to p1 ; proj₂ to p2)
open import Agda.Builtin.Sigma

open import Formula
open import Classical
open import HereAndThere

-- nested expressions
-- i.e. formulas without ⊥ and ⇒, but ⊤ and ¬ allowed
data NE : Set where
  ⊤NE   : NE
  ANE   : Var → NE
  ¬NE   : NE → NE
  _∧NE_ : NE → NE → NE
  _∨NE_ : NE → NE → NE

NE2F : NE → F
NE2F ⊤NE = ⊤
NE2F (ANE a) = V a
NE2F (¬NE f) = ¬ (NE2F f)
NE2F (f ∧NE g) = (NE2F f) ∧ (NE2F g)
NE2F (f ∨NE g) = (NE2F f) ∨ (NE2F g)

-- nested rules
-- i.e. rules where head and body are nested expressions
data NR : Set where
  _⇒NR_ : NE → NE → NR

NR2F : NR → F
NR2F (b ⇒NR h) = (NE2F b) ⇒ (NE2F h)

-- nested logic programs
NLP : Set
NLP = List NR

NLP2Th : NLP → Th
NLP2Th [] = []
NLP2Th (r ∷ lp) = (NR2F r) ∷ (NLP2Th lp)

-- theory as formula
Th2F : Th → F
Th2F [] = ⊤
Th2F (f ∷ th) = f ∧ (Th2F th)

NLP2F : NLP → F
NLP2F = λ lp → Th2F (NLP2Th lp)

-- the implication of two logic programs is equivalent to a logic program ------
-- (lemma 2)
lp⇒lp-eq-lp : (lp1 lp2 : NLP) → Σ NLP (λ lp → ValidHT ((NLP2F lp1 ⇒ NLP2F lp2) ⇔ (NLP2F lp)))
lp⇒lp-eq-lp lp1 lp2 = {!!}
