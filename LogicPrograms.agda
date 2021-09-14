module LogicPrograms where

open import Agda.Builtin.Equality
open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim)
open import Data.Sum.Base using (_⊎_ ; [_,_]) renaming (inj₁ to inl ; inj₂ to inr)
open import Data.Product using (_×_ ; _,_) renaming (proj₁ to p1 ; proj₂ to p2)
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit using (tt) renaming (⊤ to Unit)

open import Formula
open import Classical
open import HereAndThere

-- nested expressions
-- i.e. formulas without ⇒, but ⊤ and ¬ allowed
isNE : F → Set
isNE ⊥ = Unit
isNE (V a) = Unit
isNE (f ∧ g) = (isNE f) × (isNE g)
isNE (f ∨ g) = (isNE f) × (isNE g)
isNE (f ⇒ ⊥) = isNE f
isNE (f ⇒ g) = Ø

record NE : Set where
  constructor ne
  field
    nef : F
    nep : isNE nef

open NE public

-- nested rules
-- i.e. rules where head and body are nested expressions
isNR : F → Set
isNR (f ⇒ g) = (isNE f) × (isNE g)
isNR _ = Ø

record NR : Set where
  constructor nr
  field
    nrf : F
    nrp : isNR nrf

open NR public

-- nested logic programs
isNLP : Th → Set
isNLP [] = Unit
isNLP (r ∷ rs) = (isNR r) × (isNLP rs)

record NLP : Set where
  constructor nlp
  field
    nlpt : Th
    nlpp : isNLP nlpt

open NLP public

-- theory as formula
Th2F : Th → F
Th2F [] = ⊤
Th2F (f ∷ th) = f ∧ (Th2F th)

NLP2F : NLP → F
NLP2F = λ lp → Th2F (NLP2Th lp)

-- the implication of two logic programs is equivalent to a logic program ------
-- (lemma 2)
nlp⇒nlp-eq-nlp : (lp1 lp2 : NLP) → Σ NLP (λ lp → ValidHT ((Th2F (nlpt lp1) ⇒ Th2F (nlpt lp2)) ⇔ (Th2F (nlpt lp))))
nlp⇒nlp-eq-nlp (nlp [] _) (nlp lp2 lp2p) =
  (nlp lp2 lp2p) , (λ where
                    (IHT h t p) → (((λ (x , _) → x ((λ ()) , (λ ()))) ,
                                    (λ x → x (λ ()))) ,
                                   ((λ x → ((λ _ → x) , (λ _ → here-to-c x))) , (λ x → (λ _ → x)))))
nlp⇒nlp-eq-nlp (nlp ((f ⇒ g) ∷ lp1) (rp , lp1p)) (nlp lp2 lp2p) = {!!}
