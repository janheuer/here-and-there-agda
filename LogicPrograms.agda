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

-- (f ⇒ g) ⇒ (j ⇒ k) is equivalent to j ⇒ ((f ⇒ g) ⇒ k)
l2-f1 : (f g j k : F) → ValidHT (((f ⇒ g) ⇒ (j ⇒ k)) ⇔ (j ⇒ ((f ⇒ g) ⇒ k)))
l2-f1 f g j k i@(IHT h t p) =
  let
    proof⇒HT = λ (i⊧HTf⇒g×t⊧Cf⇒g→i⊧HTj⇒k×t⊧Cj⇒k , t⊧C[f⇒g]⇒j⇒k)
                 → ((λ i⊧HTj → ((λ (i⊧HTf⇒g , t⊧Cf⇒g)
                                   → (p1 (i⊧HTf⇒g×t⊧Cf⇒g→i⊧HTj⇒k×t⊧Cj⇒k (i⊧HTf⇒g , t⊧Cf⇒g))) i⊧HTj) ,
                                (λ t⊧Cf⇒g → t⊧C[f⇒g]⇒j⇒k t⊧Cf⇒g (here-to-c i⊧HTj)))) ,
                    (λ t⊧Cj t⊧Cf⇒g → t⊧C[f⇒g]⇒j⇒k t⊧Cf⇒g t⊧Cj))
    proof⇒C  = λ t⊧C[f⇒g]⇒j⇒k t⊧Cj t⊧Cf⇒g → t⊧C[f⇒g]⇒j⇒k t⊧Cf⇒g t⊧Cj
    proof⇒   = proof⇒HT , proof⇒C
    proof⇐HT = λ (i⊧HTj→[[i⊧HTf⇒g×t⊧Cf⇒g]→i⊧HTk]×[t⊧Cf⇒g⇒k] , t⊧Cj⇒[f⇒g]⇒k)
                 → (((λ (i⊧HTf⇒g , t⊧Cf⇒g)
                        → (((λ i⊧HTj
                               → (p1 (i⊧HTj→[[i⊧HTf⇒g×t⊧Cf⇒g]→i⊧HTk]×[t⊧Cf⇒g⇒k] i⊧HTj) ((i⊧HTf⇒g , t⊧Cf⇒g))))) ,
                           (λ t⊧Cj → t⊧Cj⇒[f⇒g]⇒k t⊧Cj t⊧Cf⇒g)))) ,
                    (λ t⊧Cf⇒g t⊧Cj → t⊧Cj⇒[f⇒g]⇒k t⊧Cj t⊧Cf⇒g))
    proof⇐C  = λ t⊧Cj⇒[f⇒g]⇒k t⊧Cf⇒g t⊧Cj → t⊧Cj⇒[f⇒g]⇒k t⊧Cj t⊧Cf⇒g
    proof⇐   = proof⇐HT , proof⇐C
  in
    proof⇒ , proof⇐

-- j ⇒ ((f ⇒ g) ⇒ k) is equivalent to j ⇒ (((g ∨ ¬f) ⇒ k) ∧ (k ∨ f ∨ ¬g))
-- by rem-nested⇒ (lemma 1)
l2-f2 : (f g j k : F) → ValidHT ((j ⇒ ((f ⇒ g) ⇒ k)) ⇔ (j ⇒ (((g ∨ (¬ f)) ⇒ k) ∧ (k ∨ (f ∨ (¬ g))))))
l2-f2 f g j k i@(IHT h t p) =
  let
    lemma1⇒  = rem-nested⇒ f g k i
    proof⇒C  = λ t⊧Cj⇒[f⇒g]⇒k t⊧Cj → (p2 lemma1⇒) (t⊧Cj⇒[f⇒g]⇒k t⊧Cj)
    proof⇒HT = λ (i⊧HTj→[i⊧HTf⇒g×t⊧Cf⇒g]→i⊧HTk×t⊧C[f⇒g]⇒k , t⊧Cj⇒[f⇒g]⇒k) → ((λ i⊧HTj → (p1 lemma1⇒) (i⊧HTj→[i⊧HTf⇒g×t⊧Cf⇒g]→i⊧HTk×t⊧C[f⇒g]⇒k i⊧HTj)) , proof⇒C t⊧Cj⇒[f⇒g]⇒k)
    proof⇒   = proof⇒HT , proof⇒C
    lemma1⇐  = add-nested⇒ f g k i
    proof⇐C  = λ t⊧Cj⇒[[g∨¬f]⇒k]∧[k∨f∨¬g] t⊧Cj → (p2 lemma1⇐) (t⊧Cj⇒[[g∨¬f]⇒k]∧[k∨f∨¬g] t⊧Cj)
    proof⇐HT = λ (x , t⊧Cj⇒[[g∨¬f]⇒k]∧[k∨f∨¬g]) → (((λ i⊧HTj → (p1 lemma1⇐) (x i⊧HTj))) , proof⇐C t⊧Cj⇒[[g∨¬f]⇒k]∧[k∨f∨¬g])
    proof⇐   = proof⇐HT , proof⇐C
  in
    proof⇒ , proof⇐

-- j ⇒ (((g ∨ ¬f) ⇒ k) ∧ (k ∨ f ∨ ¬g)) is equivalent to (j ⇒ ((g ∨ ¬f) ⇒ k)) ∧ (j ⇒ (k ∨ f ∨ ¬g))
l2-f3 : (f g j k : F) → ValidHT ((j ⇒ (((g ∨ (¬ f)) ⇒ k) ∧ (k ∨ (f ∨ (¬ g))))) ⇔ ((j ⇒ ((g ∨ (¬ f)) ⇒ k)) ∧ (j ⇒ (k ∨ (f ∨ (¬ g))))))
l2-f3 f g j k i@(IHT h t p) =
  let
    proof⇒C  lhs = (λ ⊧j → p1 (lhs ⊧j)) ,
                   (λ ⊧j → p2 (lhs ⊧j))
    proof⇒HT lhs = ((λ ⊧j → p1 ((p1 lhs) ⊧j)) ,
                    p1 (proof⇒C (p2 lhs))) ,
                   ((λ ⊧j → p2 ((p1 lhs) ⊧j)) ,
                    p2 (proof⇒C (p2 lhs)))
    proof⇐C  rhs = λ ⊧j → (p1 rhs) ⊧j ,
                          (p2 rhs) ⊧j
    proof⇐HT rhs = ((λ ⊧j → ((p1 (p1 rhs)) ⊧j ,
                             (p1 (p2 rhs)) ⊧j)) ,
                    proof⇐C (p2 (p1 rhs) , p2 (p2 rhs)))
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- j ⇒ ((g ∨ ¬f) ⇒ k) is equivalent to (j ∧ (g ∨ ¬f)) ⇒ k
l2-f4 : (f g j k : F) → ValidHT ((j ⇒ ((g ∨ (¬ f)) ⇒ k)) ⇔ ((j ∧ (g ∨ (¬ f))) ⇒ k))
l2-f4 f g j k i@(IHT h t p) =
  let
    proof⇒C  ⊧j⇒[g∨¬f]⇒k = λ (⊧j , ⊧g∨¬f) → ⊧j⇒[g∨¬f]⇒k ⊧j ⊧g∨¬f
    proof⇒HT ⊧j⇒[g∨¬f]⇒k = (λ (⊧j , ⊧g∨¬f) → (p1 ((p1 ⊧j⇒[g∨¬f]⇒k) ⊧j)) ⊧g∨¬f) ,
                           proof⇒C (p2 ⊧j⇒[g∨¬f]⇒k)
    proof⇐C  ⊧j∧[g∨¬f]⇒k = λ ⊧j ⊧g∨¬f → ⊧j∧[g∨¬f]⇒k (⊧j , ⊧g∨¬f)
    proof⇐HT ⊧j∧[g∨¬f]⇒k = (λ ⊧j → ((λ ⊧HTg∨¬f → (p1 ⊧j∧[g∨¬f]⇒k) (⊧j , ⊧HTg∨¬f)) ,
                                    (λ ⊧Cg∨¬f → (p2 ⊧j∧[g∨¬f]⇒k) (here-to-c ⊧j , ⊧Cg∨¬f)))) ,
                           proof⇐C (p2 ⊧j∧[g∨¬f]⇒k)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

trans⇔ : {f g j : F} → ValidHT (f ⇔ g) → ValidHT (g ⇔ j) → ValidHT (f ⇔ j)
trans⇔ f⇔g g⇔j i@(IHT h t p) =
  let
    ⊧f⇒g , ⊧g⇒f = f⇔g i
    ⊧g⇒j , ⊧j⇒g = g⇔j i
    proof⇒C  ⊧f = (p2 ⊧g⇒j) ((p2 ⊧f⇒g) ⊧f)
    proof⇒HT ⊧f = (p1 ⊧g⇒j) ((p1 ⊧f⇒g) ⊧f)
    proof⇐C  ⊧j = (p2 ⊧g⇒f) ((p2 ⊧j⇒g) ⊧j)
    proof⇐HT ⊧j = (p1 ⊧g⇒f) ((p1 ⊧j⇒g) ⊧j)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

add∧ : {f g : F} → ValidHT (f ⇔ g) → (j : F) → ValidHT ((f ∧ j) ⇔ (g ∧ j))
add∧ f⇔g j i@(IHT h t p) =
  let
    ⊧f⇒g , ⊧g⇒f = f⇔g i
    proof⇒C  = λ (⊧f , ⊧j) → (p2 ⊧f⇒g) ⊧f , ⊧j
    proof⇒HT = λ (⊧f , ⊧j) → (p1 ⊧f⇒g) ⊧f , ⊧j
    proof⇐C  = λ (⊧g , ⊧j) → (p2 ⊧g⇒f) ⊧g , ⊧j
    proof⇐HT = λ (⊧g , ⊧j) → (p1 ⊧g⇒f) ⊧g , ⊧j
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)

-- combine to (f ⇒ g) ⇒ (j ⇒ k) is equivalent to ((j ∧ (g ∨ ¬f)) ⇒ k) ∧ (j ⇒ (k ∨ f ∨ ¬g))
l2-f : (f g j k : F) → ValidHT (((f ⇒ g) ⇒ (j ⇒ k)) ⇔ (((j ∧ (g ∨ (¬ f))) ⇒ k) ∧ (j ⇒ (k ∨ (f ∨ (¬ g))))))
l2-f f g j k = trans⇔ (trans⇔ (trans⇔ (l2-f1 f g j k) (l2-f2 f g j k)) (l2-f3 f g j k)) (add∧ (l2-f4 f g j k) (j ⇒ (k ∨ (f ∨ (¬ g)))))

-- lift to nested rules
nr⇒nr-eq-nr∧nr : (p q : NR) → Σ (NR × NR) (λ (r , s) → ValidHT ((nrf p ⇒ nrf q) ⇔ (nrf r ∧ nrf s)))
nr⇒nr-eq-nr∧nr (nr (f ⇒ g) (pf , pg)) (nr (j ⇒ k) (pj , pk)) =
  let
    rf = (j ∧ (g ∨ (¬ f))) ⇒ k
    rp = (pj , (pg , pf)) , pk
    r = nr rf rp
    sf = j ⇒ (k ∨ (f ∨ (¬ g)))
    sp = pj , (pk , (pf , pg))
    s = nr sf sp
  in
    (r , s) , l2-f f g j k

-- the implication of two logic programs is equivalent to a logic program ------
-- (lemma 2)
nlp⇒nlp-eq-nlp : (lp1 lp2 : NLP) → Σ NLP (λ lp → ValidHT ((Th2F (nlpt lp1) ⇒ Th2F (nlpt lp2)) ⇔ (Th2F (nlpt lp))))
nlp⇒nlp-eq-nlp (nlp [] _) (nlp lp2 lp2p) =
  (nlp lp2 lp2p) , (λ where
                    (IHT h t p) → (((λ (x , _) → x ((λ ()) , (λ ()))) ,
                                    (λ x → x (λ ()))) ,
                                   ((λ x → ((λ _ → x) , (λ _ → here-to-c x))) , (λ x → (λ _ → x)))))
nlp⇒nlp-eq-nlp (nlp ((f ⇒ g) ∷ lp1) (rp , lp1p)) (nlp lp2 lp2p) = {!!}
