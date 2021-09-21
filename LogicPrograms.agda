module LogicPrograms where

open import Agda.Builtin.Equality
open import Data.List using (List ; _∷_ ; [] ; _++_ ; map)
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

-- combining two logic programs to a logic program with ∧, ∨, and ⇒ ----------------------
-- ∧ -----------------------------------------
-- nlp ++ nlp is a nlp
NLP++NLPisNLP : (Π1 Π2 : NLP) → isNLP ((nlpt Π1) ++ (nlpt Π2))
NLP++NLPisNLP (nlp [] _) (nlp Π2 Π2isNLP) = Π2isNLP
NLP++NLPisNLP (nlp (f ∷ Π1) Π1isNLP) Π2 = (p1 Π1isNLP) ,
                                          NLP++NLPisNLP (nlp Π1 (p2 Π1isNLP)) Π2

-- t1 ∧ t2 is equivalent to t1 ++ t2
Th∧Th-eq-Th++Th : (t1 t2 : Th) → ValidHT (((Th2F t1) ∧ (Th2F t2)) ⇔ Th2F (t1 ++ t2))
Th∧Th-eq-Th++Th [] t2 = ⊤-lid-∧ (Th2F t2)
Th∧Th-eq-Th++Th (f ∷ t1) t2 =
  let
    t1∧t2⇔t1++t2 = Th∧Th-eq-Th++Th t1 t2
  in
    trans⇔ (assoc∧ f (Th2F t1) (Th2F t2)) (replace∧rhs t1∧t2⇔t1++t2 f)

-- for lp1, lp2 : logic program there exists a logic program lp
-- s.t. lp1 ∧ lp2 is equivalent to lp
nlp∧nlp-eq-nlp : (lp1 lp2 : NLP) → Σ NLP (λ lp →
                 ValidHT ((Th2F (nlpt lp1) ∧ Th2F (nlpt lp2)) ⇔ (Th2F (nlpt lp))))
nlp∧nlp-eq-nlp Π1 Π2 =
  let
    Π = (nlpt Π1) ++ (nlpt Π2)
    ΠisNLP = NLP++NLPisNLP Π1 Π2
    Π1∧Π2⇔Π = Th∧Th-eq-Th++Th (nlpt Π1) (nlpt Π2)
  in
    nlp Π ΠisNLP , Π1∧Π2⇔Π

-- ⇒ -----------------------------------------
-- helper lemmas for proof of lp⇒lp-eq-lp
-- specifically for the case where lp1 = (f ⇒ g)

-- factor ⇒ into a theory
factor⇒Th' : F → Th → Th
factor⇒Th' f [] = []
factor⇒Th' f (g ∷ t) = (f ⇒ g) ∷ (factor⇒Th' f t)
-- factor⇒Th' produces equivalent theory
-- f ⇒ [t0, .., tn] is equivalent to [f ⇒ t0 , .., f ⇒ tn]
factor⇒Th : (f : F) → (t : Th) → ValidHT ((f ⇒ (Th2F t)) ⇔ (Th2F (factor⇒Th' f t)))
factor⇒Th f [] i@(IHT h t p) =
  let
    proof⇒C  lhs = λ ()
    proof⇒HT lhs = (λ ()) ,
                   proof⇒C (p2 lhs)
    proof⇐C  rhs = λ ⊧f → rhs
    proof⇐HT rhs = (λ ⊧f → rhs) ,
                   proof⇐C (p2 rhs)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)
factor⇒Th f (g ∷ th) i@(IHT h t p) =
  let
    ih = factor⇒Th f th i
    proof⇒C  lhs = (λ ⊧f → p1 (lhs ⊧f)) ,
                   (p2 (p1 ih)) (λ ⊧f → p2 (lhs ⊧f))
    proof⇒HT lhs = ((λ ⊧f → p1 ((p1 lhs) ⊧f)) ,
                    p1 (proof⇒C (p2 lhs))) ,
                   (p1 (p1 ih)) ((λ ⊧HTf → p2 ((p1 lhs) ⊧HTf)) ,
                                 (λ ⊧Cf → p2 ((p2 lhs) ⊧Cf)))
    proof⇐C  rhs = λ ⊧f → ((p1 rhs) ⊧f ,
                           (p2 (p2 ih)) (p2 rhs) ⊧f)
    proof⇐HT rhs = (λ ⊧f → ((p1 (p1 rhs)) ⊧f , (p1 ((p1 (p2 ih)) (p2 rhs))) ⊧f)) ,
                   proof⇐C (p2 (p1 rhs) , here-to-c (p2 rhs))
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)
-- result of factor⇒Th' is [nr ⇒ nr]
factor⇒Th:[NR⇒NR] : (r : NR) → (lp : NLP) → ((f : F) → (f ∈ (factor⇒Th' (nrf r) (nlpt lp))) → (Σ (NR × NR) (λ (ϕ , ψ) → f ≡ (nrf ϕ) ⇒ (nrf ψ))))
factor⇒Th:[NR⇒NR] r (nlp (f ∷ Π) fΠisNLP) ϕ (inl ϕ∈factor⇒) = (r , (nr f (p1 fΠisNLP))) , ϕ∈factor⇒
factor⇒Th:[NR⇒NR] r (nlp (f ∷ Π) fΠisNLP) ϕ (inr ϕ∈factor⇒) =
  let
    ih = factor⇒Th:[NR⇒NR] r (nlp Π (p2 fΠisNLP))
  in
    ih ϕ ϕ∈factor⇒

-- replace formulas of a theory by equivalent formulas
replaceTh' : ((f : F) → Σ F (λ g → ValidHT (f ⇔ g))) → Th → Th
replaceTh' τ = map (λ ϕ → p1 (τ ϕ))
-- this produces an equivalent theory
-- if t=[t0, .., tn] and f0 ⇔ t0, .., fn ⇔ tn then t ⇔ [f0, .., fn]
replaceTh : (t : Th) → (τ : (f : F) → Σ F (λ g → ValidHT (f ⇔ g))) → ValidHT ((Th2F t) ⇔ (Th2F (replaceTh' τ t)))
replaceTh [] τ = refl⇔ ⊤
replaceTh (f ∷ fs) τ i@(IHT h t p) =
  let
    (g , ⊧f⇔g) = τ f
    ((⊧HTf⇒g , ⊧Cf⇒g) , (⊧HTg⇒f , ⊧Cg⇒f)) = ⊧f⇔g i
    ((ih⇒HT , ih⇒C) , (ih⇐HT , ih⇐C)) = replaceTh fs τ i
    proof⇒C  lhs = ⊧Cf⇒g (p1 lhs) , ih⇒C (p2 lhs)
    proof⇒HT lhs = ⊧HTf⇒g (p1 lhs) , ih⇒HT (p2 lhs)
    proof⇐C  rhs = ⊧Cg⇒f (p1 rhs) , ih⇐C (p2 rhs)
    proof⇐HT rhs = ⊧HTg⇒f (p1 rhs) , ih⇐HT (p2 rhs)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)
-- actual replacement use in proof of lp⇒lp-eq-lp
replaceHelper : (f : F) → Σ F (λ g → ValidHT (f ⇔ g))
replaceHelper ((ψ1 ⇒ ψ2) ⇒ (ψ3 ⇒ ψ4)) = f⇒f-eq-f∧f' ψ1 ψ2 ψ3 ψ4
replaceHelper ψ = ψ , refl⇔ ψ
-- result of replaceTh' replaceHelper is [nr ∧ nr]
replaceTh:[NR∧NR] : (t : Th) → ((f : F) → (f ∈ t) → (Σ (NR × NR) (λ (ϕ , ψ) → f ≡ (nrf ϕ) ⇒ (nrf ψ)))) →
                    ((f : F) → (f ∈ (replaceTh' replaceHelper t)) →
                               (Σ (NR × NR) (λ (ϕ , ψ) → f ≡ (nrf ϕ) ∧ (nrf ψ))))
replaceTh:[NR∧NR] (f ∷ Γ) τ ϕ ϕ∈replace with τ f (inl refl)
replaceTh:[NR∧NR] (.((ψ1 ⇒ ψ2) ⇒ ψ3 ⇒ ψ4) ∷ Γ) τ .((ψ3 ∧ (ψ2 ∨ ψ1 ⇒ ⊥)) ⇒ ψ4 ∧ ψ3 ⇒ (ψ4 ∨ ψ1 ∨ ψ2 ⇒ ⊥)) (inl refl) | (nr (ψ1 ⇒ ψ2) (ψ1p , ψ2p) , nr (ψ3 ⇒ ψ4) (ψ3p , ψ4p)) , refl =
  (nr ((ψ3 ∧ (ψ2 ∨ (¬ ψ1))) ⇒ ψ4) ((ψ3p , (ψ2p , ψ1p)) , ψ4p) , nr (ψ3 ⇒ (ψ4 ∨ (ψ1 ∨ (¬ ψ2)))) (ψ3p , (ψ4p , (ψ1p , ψ2p)))) , refl
replaceTh:[NR∧NR] (.(nrf₁ ⇒ nrf₂) ∷ Γ) τ ϕ (inr ϕ∈replaceTh) | (nr nrf₁ nrp₁ , nr nrf₂ nrp₂) , refl =
  let
    ih = replaceTh:[NR∧NR] Γ (λ α α∈Γ → τ α (inr α∈Γ))
  in
    ih ϕ ϕ∈replaceTh

-- flatten conjunctions in a theory
flatten∧' : Th → Th
flatten∧' [] = []
flatten∧' ((f ∧ g) ∷ fs) = f ∷ g ∷ (flatten∧' fs)
flatten∧' (f       ∷ fs) = f ∷ (flatten∧' fs)
-- flatten produces an equivalent theory
-- [f0 ∧ g0, .., fn ∧ gn] is equivalent to [f0, g0, .., fn, gn]
flatten∧ : (t : Th) → ValidHT ((Th2F t) ⇔ (Th2F (flatten∧' t)))
flatten∧ [] = refl⇔ ⊤
flatten∧ ((f ∧ g) ∷ fs) i@(IHT h t p) =
  let
    (ih⇒ , ih⇐) = flatten∧ fs i
    proof⇒C  lhs = p1 (p1 lhs) , (p2 (p1 lhs) , (p2 ih⇒) (p2 lhs))
    proof⇒HT lhs = p1 (p1 lhs) , (p2 (p1 lhs) , (p1 ih⇒) (p2 lhs))
    proof⇐C  rhs = (p1 rhs , p1 (p2 rhs)) , (p2 ih⇐) (p2 (p2 rhs))
    proof⇐HT rhs = (p1 rhs , p1 (p2 rhs)) , (p1 ih⇐) (p2 (p2 rhs))
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)
flatten∧ (⊥ ∷ fs) i@(IHT h t p) =
  let
    proof⇒C  lhs = Ø-elim (p1 lhs)
    proof⇒HT lhs = Ø-elim (p1 lhs)
    proof⇐C  rhs = Ø-elim (p1 rhs)
    proof⇐HT rhs = Ø-elim (p1 rhs)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)
flatten∧ (V a ∷ fs) i@(IHT h t p) =
  let
    ((ih⇒HT , ih⇒C) , (ih⇐HT , ih⇐C)) = flatten∧ fs i
    proof⇒C  lhs = p1 lhs , ih⇒C  (p2 lhs)
    proof⇒HT lhs = p1 lhs , ih⇒HT (p2 lhs)
    proof⇐C  rhs = p1 rhs , ih⇐C  (p2 rhs)
    proof⇐HT rhs = p1 rhs , ih⇐HT (p2 rhs)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)
flatten∧ (f ∨ g ∷ fs) i@(IHT h t p) =
  let
    ((ih⇒HT , ih⇒C) , (ih⇐HT , ih⇐C)) = flatten∧ fs i
    proof⇒C  lhs = p1 lhs , ih⇒C  (p2 lhs)
    proof⇒HT lhs = p1 lhs , ih⇒HT (p2 lhs)
    proof⇐C  rhs = p1 rhs , ih⇐C  (p2 rhs)
    proof⇐HT rhs = p1 rhs , ih⇐HT (p2 rhs)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)
flatten∧ (f ⇒ g ∷ fs) i@(IHT h t p) =
  let
    ((ih⇒HT , ih⇒C) , (ih⇐HT , ih⇐C)) = flatten∧ fs i
    proof⇒C  lhs = p1 lhs , ih⇒C  (p2 lhs)
    proof⇒HT lhs = p1 lhs , ih⇒HT (p2 lhs)
    proof⇐C  rhs = p1 rhs , ih⇐C  (p2 rhs)
    proof⇐HT rhs = p1 rhs , ih⇐HT (p2 rhs)
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)
-- result of flatten∧' is [nr]
flatten∧:[NR] : (t : Th) → ((f : F) → (f ∈ t) → (Σ (NR × NR) (λ (ϕ , ψ) → f ≡ (nrf ϕ) ∧ (nrf ψ)))) →
                    ((f : F) → (f ∈ (flatten∧' t)) → (isNR f))
flatten∧:[NR] (f ∷ Γ) τ ϕ abc with τ f (inl refl)
flatten∧:[NR] (.(nrf₁ ∧ nrf₂) ∷ Γ) τ .nrf₁ (inl refl) | (nr nrf₁ nrp₁ , nr nrf₂ nrp₂) , refl = nrp₁
flatten∧:[NR] (.(nrf₁ ∧ nrf₂) ∷ Γ) τ .nrf₂ (inr (inl refl)) | (nr nrf₁ nrp₁ , nr nrf₂ nrp₂) , refl = nrp₂
flatten∧:[NR] (.(nrf₁ ∧ nrf₂) ∷ Γ) τ ϕ (inr (inr ϕ∈flatten∧)) | (nr nrf₁ nrp₁ , nr nrf₂ nrp₂) , refl =
  let
    ih = flatten∧:[NR] Γ (λ α α∈Γ → τ α (inr α∈Γ))
  in
    ih ϕ ϕ∈flatten∧

-- given [nr] there is an equivalent lp
[NR]2NLP : (t : Th) → ((f : F) → (f ∈ t) → (isNR f)) → (Σ NLP (λ Π → ValidHT ((Th2F t) ⇔ (Th2F (nlpt Π)))))
[NR]2NLP [] σ = (nlp [] tt) , refl⇔ ⊤
[NR]2NLP (f ∷ t) σ =
  let
    rec = [NR]2NLP t (λ g g∈t → σ g (inr g∈t))
    Π = nlpt (p1 rec)
    ΠisNLP = nlpp (p1 rec)
    t⇔Π = p2 rec
  in
    (nlp (f ∷ Π) (σ f (inl refl) , ΠisNLP)) , (replace∧rhs t⇔Π f)

-- for lp1, lp2 : logic program there exists a logic program lp
-- s.t. lp1 ⇒ lp2 is equivalent to lp
nlp⇒nlp-eq-nlp : (lp1 lp2 : NLP) → Σ NLP (λ lp →
                 ValidHT ((Th2F (nlpt lp1) ⇒ Th2F (nlpt lp2)) ⇔ (Th2F (nlpt lp))))
-- [] ⇒ lp2 = ⊤ ⇒ lp2 =(by ⊤-lid-⇒) lp2
nlp⇒nlp-eq-nlp (nlp [] _) (nlp lp2 lp2p) = (nlp lp2 lp2p) , ⊤-lid-⇒ (Th2F lp2)
nlp⇒nlp-eq-nlp (nlp ((f ⇒ g) ∷ []) (rp , _)) (nlp lp2 lp2p) =
  let
    -- 1) lhs eq. (f ⇒ g) ⇒ [t0, .., tn]
    -- 2)     eq. [(f ⇒ g) ⇒ t0, .., (f ⇒ g) ⇒ tn] by factor⇒Th
    -- 3)     eq. [  ϕ0 ∧ ψ0   , ..,  ϕn ∧ ψn    ] by replaceTh with nr⇒nr-eq-nr∧nr
    -- 4)     eq. [  ϕ0 , ψ0,    ..,  ϕn , ψn    ] by flatten∧
    -- 5) [ϕ0, ψ0, .., ϕn, ψn] is a logic programs

    -- 1) lhs ⇔ Π1
    -- Π1 = [f⇒g] ⇒ lp2
    -- lhs = Th2F ((f ⇒ g) ∷ []) ⇒ Th2F lp2
    --     = ((f ⇒ g) ∧ ⊤) ⇒ Th2F lp2
    -- ⊤-rid-∧ (f ⇒ g) = ValidHT ((f ⇒ g) ⇔ ((f ⇒ g) ∧ ⊤))
    lhs⇔Π1 = replace⇒lhs (⊤-rid-∧ (f ⇒ g)) (Th2F lp2)

    -- 2) Π1 ⇔ Π2
    -- Π2 = factor (f⇒g) ⇒ into theory lp2
    Π2 = factor⇒Th' (f ⇒ g) lp2
    -- Π2 contains only implications of rules
    Π2is[NR⇒NR] = factor⇒Th:[NR⇒NR] (nr (f ⇒ g) rp) (nlp lp2 lp2p)
    Π1⇔Π2 = factor⇒Th (f ⇒ g) lp2

    -- 3) Π2 ⇔ Π3
    -- Π3 = replace implication of two rules by conjunction of two rules in Π2
    -- (see f⇒f-eq-f∧f)
    Π3 = replaceTh' replaceHelper Π2
    -- Π3 contains only conjunctions of rules
    Π3is[NR∧NR] = replaceTh:[NR∧NR] Π2 Π2is[NR⇒NR]
    Π2⇔Π3 = replaceTh Π2 replaceHelper

    -- 4) Π3 ⇔ Π4
    -- Π4 = flatten conjunctions in the theory Π3
    Π4 = flatten∧' Π3
    -- Π4 contains only rules
    Π4is[NR] = flatten∧:[NR] Π3 Π3is[NR∧NR]
    Π3⇔Π4 = flatten∧ Π3

    -- 5) Π4 ⇔ Π with Π logic program
    -- as Π4 contains only rules there is an equivalent lp Π
    ((nlp Π ΠisNLP) , Π4⇔Π) = [NR]2NLP Π4 Π4is[NR]
    -- lhs ⇔ Π by 1-5
    lhs⇔Π = trans⇔ (trans⇔ (trans⇔ (trans⇔ lhs⇔Π1
                                              Π1⇔Π2)
                                              Π2⇔Π3)
                                              Π3⇔Π4)
                                              Π4⇔Π
  in
    (nlp Π ΠisNLP) , lhs⇔Π
nlp⇒nlp-eq-nlp (nlp ((f ⇒ g) ∷ lp1) (rp , lp1p)) (nlp lp2 lp2p) =
  let
    -- 1) lp1 ⇒ lp2 is equivalent to a logic program Π1 by induction
    -- 2) (f⇒g) ⇒ Π1 is equivalent to a logic program Π2 by induction
    -- 3) (f⇒g) ⇒ (lp1⇒lp2) is equivalent to Π2 by combining 1) and 2)
    -- 4) lhs = Th2F ((f⇒g) ∷ lp1) ⇒ lp2 = ((f⇒g) ∧ lp1) ⇒ lp2 is equivalent to Π2

    -- 1) lp1 ⇒ lp2 is equivalent to Π1
    ((nlp Π1 Π1isNLP) , lp1⇒lp2⇔Π1) = nlp⇒nlp-eq-nlp (nlp lp1 lp1p) (nlp lp2 lp2p)

    -- 2) (f⇒g) ⇒ Π1 is equivalent to Π2
    -- due to definition of Th2F ((f ⇒ g) ∷ []) it is actually
    -- ((f⇒g) ∧ ⊤) ⇒ Π1 is equivalent to Π2
    ((nlp Π2 Π2isNLP) , [[f⇒g]∧⊤]⇒Π1⇔Π2) = nlp⇒nlp-eq-nlp (nlp ((f ⇒ g) ∷ []) (rp , tt)) (nlp Π1 Π1isNLP)
    -- (f⇒g) ⇒ Π1 is equivalent to ((f⇒g) ∧ ⊤) ⇒ Π1
    [f⇒g]⇒Π1⇔[[f⇒g]∧⊤]⇒Π1 = replace⇒lhs (symm⇔ (⊤-rid-∧ (f ⇒ g))) (Th2F Π1)
    -- (f⇒g) ⇒ Π1 is equivalent to Π2
    [f⇒g]⇒Π1⇔Π2 = trans⇔ [f⇒g]⇒Π1⇔[[f⇒g]∧⊤]⇒Π1
                                    [[f⇒g]∧⊤]⇒Π1⇔Π2
    -- Π2 is the needed logic program
    -- it remains to show that (f⇒g) ∷ lp1 ⇒ lp2 is equivalent to Π2
    -- (f⇒g) ∷ lp1= ((f⇒g) ∧ lp1)

    -- 3) (f⇒g) ⇒ (lp1⇒lp2) is equivalent to Π2
    -- (f⇒g) ⇒ (lp1⇒lp2) is equivalent to (f⇒g) ⇒ Π1
    [f⇒g]⇒[lp1⇒lp2]⇔[f⇒g]⇒Π1 = replace⇒rhs lp1⇒lp2⇔Π1 (f ⇒ g)
    -- (f⇒g) ⇒ (lp1⇒lp2) is equivalent to Π2
    [f⇒g]⇒[lp1⇒lp2]⇔Π2 = trans⇔ [f⇒g]⇒[lp1⇒lp2]⇔[f⇒g]⇒Π1 [f⇒g]⇒Π1⇔Π2

    -- 4) ((f⇒g) ∧ lp1) ⇒ lp2 is equivalent to Π2
    -- ((f⇒g) ∧ lp1) ⇒ lp2 is equivalent to (f⇒g) ⇒ (lp1⇒lp2)
    [[f⇒g]∧lp1]⇒lp2⇔[f⇒g]⇒[lp1⇒lp2] = symm⇔ (uncurry (f ⇒ g) (Th2F lp1) (Th2F lp2))
    -- ((f⇒g) ∧ lp1) ⇒ lp2 is equivalent to Π2
    [[f⇒g]∧lp1]⇒lp2⇔Π2 = trans⇔ [[f⇒g]∧lp1]⇒lp2⇔[f⇒g]⇒[lp1⇒lp2]
                                                  [f⇒g]⇒[lp1⇒lp2]⇔Π2
  in
    (nlp Π2 Π2isNLP) , [[f⇒g]∧lp1]⇒lp2⇔Π2

-- for every theory there exists a equivalent nested logic program -----------------------
-- (theorem 1)

-- nlp ++ nlp is a nlp
NLP++NLPisNLP : (Π1 Π2 : NLP) → isNLP ((nlpt Π1) ++ (nlpt Π2))
NLP++NLPisNLP (nlp [] _) (nlp Π2 Π2isNLP) = Π2isNLP
NLP++NLPisNLP (nlp (f ∷ Π1) Π1isNLP) Π2 = (p1 Π1isNLP) , NLP++NLPisNLP (nlp Π1 (p2 Π1isNLP)) Π2

-- t1 ∧ t2 is equivalent to t1 ++ t2
Th∧Th-eq-Th++Th : (t1 t2 : Th) → ValidHT (((Th2F t1) ∧ (Th2F t2)) ⇔ Th2F (t1 ++ t2))
Th∧Th-eq-Th++Th [] t2 = ⊤-lid-∧ (Th2F t2)
Th∧Th-eq-Th++Th (f ∷ t1) t2 =
  let
    t1∧t2⇔t1++t2 = Th∧Th-eq-Th++Th t1 t2
  in
    trans⇔ (assoc∧ f (Th2F t1) (Th2F t2)) (replace∧rhs t1∧t2⇔t1++t2 f)

-- if f⇔t1 and g⇔t2 then f∧g ⇔ t1++t2
combineF⇔Th : {f g : F} → {t1 t2 : Th} → ValidHT (f ⇔ (Th2F t1)) → ValidHT (g ⇔ (Th2F t2)) → ValidHT ((f ∧ g) ⇔ (Th2F (t1 ++ t2)))
combineF⇔Th {f} {g} {t1} {t2} f⇔t1 g⇔t2 = trans⇔ (trans⇔ (replace∧lhs f⇔t1 g) (replace∧rhs g⇔t2 (Th2F t1))) (Th∧Th-eq-Th++Th t1 t2)

-- for every theory Γ there exists nested logic program Π s.t. Γ ⇔ Π
th-eq-nlp : (Γ : Th) → Σ NLP (λ Π → ValidHT ((Th2F Γ) ⇔ (Th2F (nlpt Π))))
th-eq-nlp [] = (nlp [] tt) , refl⇔ ⊤
th-eq-nlp (⊥ ∷ []) = (nlp ((⊤ ⇒ ⊥) ∷ []) ((tt , tt) , tt)) ,
                     trans⇔ (trans⇔ (⊥∧eq⊥ (Th2F [])) (symm⇔ fact⊥eq⊥)) (symm⇔ (⊤-rid-∧ (⊤ ⇒ ⊥)))
th-eq-nlp ((V a) ∷ []) = (nlp ((⊤ ⇒ (V a)) ∷ []) ((tt , tt) , tt)) ,
                         replace∧lhs (symm⇔ (⊤-lid-⇒ (V a))) ⊤
th-eq-nlp ((f ∧ g) ∷ []) =
  let
    (Πf , f∧⊤⇔Πf) = th-eq-nlp (f ∷ [])
    f⇔Πf = trans⇔ (symm⇔ (⊤-rid-∧ f)) f∧⊤⇔Πf
    (Πg , g∧⊤⇔Πg) = th-eq-nlp (g ∷ [])
    g⇔Πg = trans⇔ (symm⇔ (⊤-rid-∧ g)) g∧⊤⇔Πg
    Π = (nlpt Πf) ++ (nlpt Πg)
    ΠisNLP = NLP++NLPisNLP Πf Πg
    [f∧g]⇔Πf++Πg = trans⇔ (⊤-rid-∧ (f ∧ g)) (combineF⇔Th f⇔Πf g⇔Πg)
  in
    nlp Π ΠisNLP , [f∧g]⇔Πf++Πg
th-eq-nlp ((f ∨ g) ∷ []) =
  let
    ∨2⇒[f∨g] = ((f ⇒ g) ⇒ g) ∧ ((g ⇒ f) ⇒ f)
    ((nlp Π ΠisNLP) , ∨2⇒[f∨g]⇔Π) = th-eq-nlp (∨2⇒[f∨g] ∷ [])
    f∨g⇔Π = trans⇔ (replace∧lhs (∨2⇒ f g) ⊤) ∨2⇒[f∨g]⇔Π
  in
    ((nlp Π ΠisNLP) , f∨g⇔Π)
th-eq-nlp ((f ⇒ g) ∷ []) =
  let
    (Πf , f∧⊤⇔Πf) = th-eq-nlp (f ∷ [])
    f⇔Πf = trans⇔ (symm⇔ (⊤-rid-∧ f)) f∧⊤⇔Πf
    (Πg , g∧⊤⇔Πg) = th-eq-nlp (g ∷ [])
    g⇔Πg = trans⇔ (symm⇔ (⊤-rid-∧ g)) g∧⊤⇔Πg
    (Π  , Πf⇒Πg⇔Π) = nlp⇒nlp-eq-nlp Πf Πg
    [f⇒g]⇔Π = trans⇔ (trans⇔ (trans⇔ (⊤-rid-∧ (f ⇒ g)) (replace⇒lhs f⇔Πf g)) (replace⇒rhs g⇔Πg (Th2F (nlpt Πf)))) Πf⇒Πg⇔Π
  in
    Π , [f⇒g]⇔Π
th-eq-nlp (f ∷ Γ) =
  let
    (Πf , f⇔Πf) = th-eq-nlp (f ∷ [])
    (ΠΓ , Γ⇔ΠΓ) = th-eq-nlp Γ
    Π = (nlpt Πf) ++ (nlpt ΠΓ)
    ΠisNLP = NLP++NLPisNLP Πf ΠΓ
    f∷Γ⇔Π = combineF⇔Th (trans⇔ (symm⇔ (⊤-rid-∧ f)) f⇔Πf) Γ⇔ΠΓ
  in
    nlp Π ΠisNLP , f∷Γ⇔Π
