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

-- the implication of two logic programs is equivalent to a logic program ----------------
-- (lemma 2)

-- lift f⇒f-eq-f∧f to nested rules
nr⇒nr-eq-nr∧nr : (p q : NR) → Σ (NR × NR) (λ (r , s) →
                 ValidHT ((nrf p ⇒ nrf q) ⇔ (nrf r ∧ nrf s)))
nr⇒nr-eq-nr∧nr (nr (f ⇒ g) (pf , pg)) (nr (j ⇒ k) (pj , pk)) =
  let
    rf = (j ∧ (g ∨ (¬ f))) ⇒ k
    rp = (pj , (pg , pf)) , pk
    r = nr rf rp
    sf = j ⇒ (k ∨ (f ∨ (¬ g)))
    sp = pj , (pk , (pf , pg))
    s = nr sf sp
  in
    (r , s) , f⇒f-eq-f∧f f g j k

nlp⇒nlp-eq-nlp : (lp1 lp2 : NLP) →
                 Σ NLP (λ lp → ValidHT ((Th2F (nlpt lp1) ⇒ Th2F (nlpt lp2)) ⇔
                                        (Th2F (nlpt lp))))
nlp⇒nlp-eq-nlp (nlp [] _) (nlp lp2 lp2p) =
  (nlp lp2 lp2p) , (λ where
                    (IHT h t p) → (((λ (x , _) → x ((λ ()) , (λ ()))) ,
                                    (λ x → x (λ ()))) ,
                                   ((λ x → ((λ _ → x) , (λ _ → here-to-c x))) ,
                                    (λ x → (λ _ → x)))))
nlp⇒nlp-eq-nlp (nlp ((f ⇒ g) ∷ lp1) (rp , lp1p)) (nlp lp2 lp2p) = {!!}
