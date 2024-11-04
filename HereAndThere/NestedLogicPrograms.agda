module HereAndThere.NestedLogicPrograms where

open import Data.List using (_++_ ; map)

open import HereAndThere
open import Formula.WithoutDisjunction
open import Formula.LogicPrograms.Nested

-- the conjunction of two nested logic programs is a nested logic program ------
-- nlp ++ nlp is a nlp
NLP++NLPisNLP : (Π1 Π2 : NLP) → isNLP ((nlpt Π1) ++ (nlpt Π2))
NLP++NLPisNLP (nlp [] _) (nlp Π2 Π2isNLP) = Π2isNLP
NLP++NLPisNLP (nlp (f ∷ Π1) (fisNR , Π1isNLP)) Π2 =
  fisNR , NLP++NLPisNLP (nlp Π1 Π1isNLP) Π2

-- t1 ∧ t2 is equivalent to t1 ++ t2
Th∧Th-eq-Th++Th : (t1 t2 : Th) →
                  ((Th2F t1) ∧ (Th2F t2)) ≡HT Th2F (t1 ++ t2)
Th∧Th-eq-Th++Th [] t2 = ⊤-lid-∧
Th∧Th-eq-Th++Th (f ∷ t1) t2 =
  (f ∧ Th2F t1) ∧ Th2F t2 ≡HT⟨ assoc∧ ⟩
  f ∧ (Th2F t1 ∧ Th2F t2) ≡HT⟨ replace∧rhs (Th∧Th-eq-Th++Th t1 t2) ⟩
  f ∧ Th2F (t1 ++ t2)     ■

-- for lp1, lp2 : nested logic program there exists a nested logic program lp
-- s.t. lp1 ∧ lp2 is equivalent to lp
nlp∧nlp-eq-nlp : (lp1 lp2 : NLP) → Σ NLP (λ lp →
                 (NLP2F lp1 ∧ NLP2F lp2) ≡HT (NLP2F lp))
nlp∧nlp-eq-nlp Π1 Π2 =
  let
    Π = (nlpt Π1) ++ (nlpt Π2)
    ΠisNLP = NLP++NLPisNLP Π1 Π2
    Π1∧Π2⇔Π = Th∧Th-eq-Th++Th (nlpt Π1) (nlpt Π2)
  in
    nlp Π ΠisNLP , Π1∧Π2⇔Π

-- the implication of two nested logic programs is a nested logic program ------
-- helper lemmas for proof of nlp⇒nlp-eq-nlp
-- specifically for the case where lp1 = (f ⇒ g)

-- factor ⇒ into a theory
factor⇒Th' : F → Th → Th
factor⇒Th' f []      = []
factor⇒Th' f (g ∷ t) = (f ⇒ g) ∷ (factor⇒Th' f t)
-- factor⇒Th' produces equivalent theory
-- f ⇒ [t0, .., tn] is equivalent to [f ⇒ t0 , .., f ⇒ tn]
factor⇒Th : (f : F) → (t : Th) →
            (f ⇒ (Th2F t)) ≡HT (Th2F (factor⇒Th' f t))
factor⇒Th f [] i@(IHT h t p) =
  let
    proof⇒C  = λ _ ()
    proof⇒HT = λ (_ , ⊧Cf⇒⊤) → (λ ()) , proof⇒C ⊧Cf⇒⊤
    proof⇐C  = λ ⊧⊤ ⊧f → ⊧⊤
    proof⇐HT = λ (⊧HT⊤ , ⊧C⊤) → (λ ⊧f → (⊧HT⊤ , ⊧C⊤)) , proof⇐C ⊧C⊤
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)
factor⇒Th f (g ∷ th) i@(IHT h t p) =
  let
    ((ih⇒HT , ih⇒C) , (ih⇐HT , ih⇐C)) = factor⇒Th f th i
    proof⇒C  = λ ⊧f⇒g∧th → (λ ⊧f → p1 (⊧f⇒g∧th ⊧f)) ,
                           (ih⇒C (λ ⊧f → p2 (⊧f⇒g∧th ⊧f)))
    proof⇒HT = λ (⊧HTf⇒g∧th , ⊧Cf⇒g∧th)
                 → ((λ ⊧f → p1 (⊧HTf⇒g∧th ⊧f)) , (p1 (proof⇒C ⊧Cf⇒g∧th))) ,
                   (ih⇒HT ((λ ⊧HTf → p2 (⊧HTf⇒g∧th ⊧HTf)) ,
                           (λ ⊧Cf  → p2 (⊧Cf⇒g∧th  ⊧Cf))))
    proof⇐C  = λ (⊧f⇒g , ⊧[f⇒ti]) ⊧f → (⊧f⇒g ⊧f , ih⇐C ⊧[f⇒ti] ⊧f)
    proof⇐HT = λ ((⊧HTf⇒g , ⊧Cf⇒g) , ⊧[f⇒ti])
                 → (λ ⊧f → (⊧HTf⇒g ⊧f , (p1 (ih⇐HT ⊧[f⇒ti])) ⊧f)) ,
                   (proof⇐C (⊧Cf⇒g , ht-to-c ⊧[f⇒ti]))
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)
-- result of factor⇒Th' is [nr ⇒ nr]
factor⇒Th:[NR⇒NR] : (r : NR) → (lp : NLP) →
                    ((f : F) → (f ∈ (factor⇒Th' (nrf r) (nlpt lp))) →
                    (Σ (NR × NR) (λ (ϕ , ψ) → f ≡ (nrf ϕ) ⇒ (nrf ψ))))
factor⇒Th:[NR⇒NR] r (nlp (f ∷ _) (fisNR , _)) .((nrf r) ⇒ f) (inl refl) =
  (r , (nr f fisNR)) , refl
factor⇒Th:[NR⇒NR] r (nlp (_ ∷ Π) (_ , ΠisNLP)) ϕ (inr ϕ∈factor⇒) =
  let
    ih = factor⇒Th:[NR⇒NR] r (nlp Π ΠisNLP)
  in
    ih ϕ ϕ∈factor⇒

-- replace formulas of a theory by equivalent formulas
replaceTh' : ((f : F) → Σ F (λ g → f ≡HT g)) → Th → Th
replaceTh' τ = map (λ ϕ → p1 (τ ϕ))
-- this produces an equivalent theory
-- if t=[t0, .., tn] and f0 ⇔ t0, .., fn ⇔ tn then t ⇔ [f0, .., fn]
replaceTh : (t : Th) → (τ : (f : F) → Σ F (λ g → ValidHT (f ⇔ g))) →
            (Th2F t) ≡HT (Th2F (replaceTh' τ t))
replaceTh [] τ = refl⇔
replaceTh (f ∷ fs) τ i@(IHT h t p) =
  let
    (g , ⊧f⇔g) = τ f
    ((⊧HTf⇒g , ⊧Cf⇒g) , (⊧HTg⇒f , ⊧Cg⇒f)) = ⊧f⇔g i
    ((ih⇒HT , ih⇒C) , (ih⇐HT , ih⇐C)) = replaceTh fs τ i
    proof⇒C  = λ (⊧f , ⊧fs) → ⊧Cf⇒g  ⊧f , ih⇒C  ⊧fs
    proof⇒HT = λ (⊧f , ⊧fs) → ⊧HTf⇒g ⊧f , ih⇒HT ⊧fs
    proof⇐C  = λ (⊧g , ⊧replace[fs]) → ⊧Cg⇒f  ⊧g , ih⇐C  ⊧replace[fs]
    proof⇐HT = λ (⊧g , ⊧replace[fs]) → ⊧HTg⇒f ⊧g , ih⇐HT ⊧replace[fs]
  in
    (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)
-- actual replacement use in proof of lp⇒lp-eq-lp
replaceHelper : (f : F) → Σ F (λ g → f ≡HT g)
replaceHelper ((ψ1 ⇒ ψ2) ⇒ (ψ3 ⇒ ψ4)) = f⇒f-eq-f∧fΣ ψ1 ψ2 ψ3 ψ4
replaceHelper ψ = ψ , refl⇔
-- result of replaceTh' replaceHelper is [nr ∧ nr]
replaceTh:[NR∧NR] : (t : Th) → ((f : F) → (f ∈ t) → (Σ (NR × NR) (λ (ϕ , ψ) →
                                f ≡ (nrf ϕ) ⇒ (nrf ψ)))) →
                    ((f : F) → (f ∈ (replaceTh' replaceHelper t)) →
                     (Σ (NR × NR) (λ (ϕ , ψ) → f ≡ (nrf ϕ) ∧ (nrf ψ))))
replaceTh:[NR∧NR] (f ∷ Γ) τ
  .(p1 (replaceHelper f)) (inl refl) with τ f (inl refl)
... | (nr (ψ1 ⇒ ψ2) (ψ1p , ψ2p) , nr (ψ3 ⇒ ψ4) (ψ3p , ψ4p)) , refl =
  (nr ((ψ3 ∧ (ψ2 ∨ (¬ ψ1))) ⇒ ψ4) ((ψ3p , (ψ2p , ψ1p)) , ψ4p) ,
   nr (ψ3 ⇒ (ψ4 ∨ (ψ1 ∨ (¬ ψ2)))) (ψ3p , (ψ4p , (ψ1p , ψ2p))) ) ,
  refl
replaceTh:[NR∧NR] (f ∷ Γ) τ ϕ (inr ϕ∈replaceΓ) =
  let
    ih = replaceTh:[NR∧NR] Γ (λ α α∈Γ → τ α (inr α∈Γ))
  in
    ih ϕ ϕ∈replaceΓ

-- flatten conjunctions in a theory
flatten∧' : Th → Th
flatten∧' [] = []
flatten∧' ((f ∧ g) ∷ fs) = f ∷ g ∷ (flatten∧' fs)
flatten∧' (f       ∷ fs) = f ∷ (flatten∧' fs)
-- flatten produces an equivalent theory
-- [f0 ∧ g0, .., fn ∧ gn] is equivalent to [f0, g0, .., fn, gn]
flatten∧ : (t : Th) → (Th2F t) ≡HT (Th2F (flatten∧' t))
flatten∧ [] = refl⇔
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
flatten∧:[NR] : (t : Th) → ((f : F) → (f ∈ t) → (Σ (NR × NR) (λ (ϕ , ψ) →
                            f ≡ (nrf ϕ) ∧ (nrf ψ)))) →
                    ((f : F) → (f ∈ (flatten∧' t)) → (isNR f))
flatten∧:[NR] (f ∷ Γ) τ ϕ _ with τ f (inl refl)
flatten∧:[NR] (.(r1 ∧ _) ∷ Γ) τ .r1 (inl refl)
  | (nr r1 r1p , _) , refl = r1p
flatten∧:[NR] (.(_ ∧ r2) ∷ Γ) τ .r2 (inr (inl refl))
  | (_ , nr r2 r2p) , refl = r2p
flatten∧:[NR] (.(_ ∧ _) ∷ Γ) τ ϕ (inr (inr ϕ∈flatten∧Γ))
  | (_ , _) , refl =
  let
    ih = flatten∧:[NR] Γ (λ α α∈Γ → τ α (inr α∈Γ))
  in
    ih ϕ ϕ∈flatten∧Γ

-- given [nr] there is an equivalent nlp
[NR]2NLP : (t : Th) → ((f : F) → (f ∈ t) → (isNR f)) →
           Σ NLP (λ Π → (Th2F t) ≡HT (NLP2F Π))
[NR]2NLP [] σ = (nlp [] tt) , refl⇔
[NR]2NLP (f ∷ t) σ =
  let
    (nlp Π' Π'isNLP , t⇔Π') = [NR]2NLP t (λ g g∈t → σ g (inr g∈t))
    Π = nlp (f ∷ Π') (σ f (inl refl) , Π'isNLP)
    f∷t⇔f∷Π = Th2F (f ∷ t) ≡HT⟨def⟩
               f ∧ Th2F t  ≡HT⟨ replace∧rhs t⇔Π' ⟩
               f ∧ Th2F Π' ≡HT⟨def⟩
                 NLP2F Π   ■
  in
    -- f ∧ t ⇔ f ∧ Π
    Π , f∷t⇔f∷Π

-- for lp1, lp2 : logic program there exists a nested logic program lp
-- s.t. lp1 ⇒ lp2 is equivalent to lp
-- (lemma 2)
nlp⇒nlp-eq-nlp : (lp1 lp2 : NLP) → Σ NLP (λ lp →
                 (NLP2F lp1 ⇒ NLP2F lp2) ≡HT (NLP2F lp))
-- [] ⇒ lp2 = ⊤ ⇒ lp2 =(by ⊤-lid-⇒) lp2
nlp⇒nlp-eq-nlp (nlp [] tt) lp2 = lp2 , ⊤-lid-⇒
nlp⇒nlp-eq-nlp (nlp ((f ⇒ g) ∷ []) (rp , tt)) (nlp lp2 lp2p) =
  let
    -- 1) (f⇒g) ⇒ [t0, .., tn] eq. Π1 = [(f⇒g) ⇒ t0, .., (f⇒g) ⇒ tn]
    --                         by factor⇒Th
    Π1 = factor⇒Th' (f ⇒ g) lp2
    -- Π1 contains only implications of rules
    Π1is[NR⇒NR] = factor⇒Th:[NR⇒NR] (nr (f ⇒ g) rp) (nlp lp2 lp2p)
    -- 2) Π1 eq. Π2 = [  ϕ0 ∧ ψ0 , ..,  ϕn ∧ ψn  ]
    --       by replaceTh with f⇒f-eq-f∧fΣ
    Π2 = replaceTh' replaceHelper Π1
    -- Π2 contains only conjunctions of rules
    Π2is[NR∧NR] = replaceTh:[NR∧NR] Π1 Π1is[NR⇒NR]
    -- 3) Π2 eq. Π3 = [  ϕ0 , ψ0 , ..,  ϕn , ψn  ]
    --       by flatten∧
    Π3 = flatten∧' Π2
    -- Π3 contains only rules
    Π3is[NR] = flatten∧:[NR] Π2 Π2is[NR∧NR]
    -- 4) Π3 is a nested logic programs
    (Π , Π3⇔Π) = [NR]2NLP Π3 Π3is[NR]

    proof =
      Th2F ((f ⇒ g) ∷ []) ⇒ Th2F lp2 ≡HT⟨def⟩
      ((f ⇒ g) ∧ ⊤) ⇒ Th2F lp2       ≡HT⟨ replace⇒lhs ⊤-rid-∧ ⟩
       (f ⇒ g)      ⇒ Th2F lp2       ≡HT⟨ factor⇒Th (f ⇒ g) lp2 ⟩      -- 1)
                 Th2F Π1             ≡HT⟨ replaceTh Π1 replaceHelper ⟩ -- 2)
                 Th2F Π2             ≡HT⟨ flatten∧ Π2 ⟩                -- 3)
                 Th2F Π3             ≡HT⟨ Π3⇔Π ⟩                       -- 4)
                 NLP2F Π             ■
  in
    Π , proof
nlp⇒nlp-eq-nlp (nlp ((f ⇒ g) ∷ lp1) (rp , lp1p)) (nlp lp2 lp2p) =
  let
    -- lp1 ⇒ lp2 is equivalent to a nested logic program Π' by induction
    (Π' , lp1⇒lp2⇔Π') = nlp⇒nlp-eq-nlp (nlp lp1 lp1p) (nlp lp2 lp2p)
    -- (f⇒g) ⇒ Π' is equivalent to a nested logic program Π by induction
    (Π , [f⇒g]⇒Π'⇔Π) = nlp⇒nlp-eq-nlp (nlp ((f ⇒ g) ∷ []) (rp , tt)) Π'
    proof =
      Th2F ((f ⇒ g) ∷ lp1)      ⇒ Th2F lp2 ≡HT⟨def⟩
      ((f ⇒ g)      ∧ Th2F lp1) ⇒ Th2F lp2 ≡HT⟨ curry ⟩
       (f ⇒ g)      ⇒ Th2F lp1  ⇒ Th2F lp2 ≡HT⟨ replace⇒rhs lp1⇒lp2⇔Π' ⟩
       (f ⇒ g)      ⇒       NLP2F Π'       ≡HT⟨ replace⇒lhs (symm⇔ ⊤-rid-∧) ⟩
      ((f ⇒ g) ∧ ⊤) ⇒       NLP2F Π'       ≡HT⟨def⟩
      Th2F ((f ⇒ g) ∷ []) ⇒ NLP2F Π'       ≡HT⟨ [f⇒g]⇒Π'⇔Π ⟩
                       NLP2F Π             ■
  in
    Π , proof

-- for every theory there exists a equivalent nested logic program -------------
-- (theorem 1)

-- for every formula ϕ without disjunction,
-- there exists a nested logic program Π s.t. ϕ ⇔ Π
f\∨-eq-nlp : (ϕ : F\∨) → Σ NLP (λ Π → (f\∨f ϕ) ≡HT (NLP2F Π))
f\∨-eq-nlp (f\∨ ⊥ tt) =
  let
    -- Π = { ⊥. }
    Π = nlp ((⊤ ⇒ ⊥) ∷ []) ((tt , tt) , tt)
    ⊥⇔Π =            ⊥        ≡HT⟨ ⊤-lid-⇒ ⟩ˢ
                 ⊤ ⇒ ⊥        ≡HT⟨ ⊤-rid-∧ ⟩ˢ
                (⊤ ⇒ ⊥) ∧ ⊤   ≡HT⟨def⟩
          Th2F ((⊤ ⇒ ⊥) ∷ []) ≡HT⟨def⟩
                 NLP2F Π      ■
  in
    Π , ⊥⇔Π
f\∨-eq-nlp (f\∨ (V a) tt) =
  let
    -- Π = { a. }
    Π = nlp ((⊤ ⇒ (V a)) ∷ []) ((tt , tt) , tt)
    a⇔Π =             V a         ≡HT⟨ ⊤-lid-⇒ ⟩ˢ
                 ⊤ ⇒ (V a)        ≡HT⟨ ⊤-rid-∧ ⟩ˢ
                (⊤ ⇒ (V a)) ∧ ⊤   ≡HT⟨def⟩
          Th2F ((⊤ ⇒ (V a)) ∷ []) ≡HT⟨def⟩
                   NLP2F Π        ■
  in
    Π , a⇔Π
f\∨-eq-nlp (f\∨ (ϕ ∧ ψ) (ϕp , ψp)) =
  let
    (Πϕ , ϕ⇔Πϕ) = f\∨-eq-nlp (f\∨ ϕ ϕp)
    (Πψ , ψ⇔Πψ) = f\∨-eq-nlp (f\∨ ψ ψp)
    (Π , Πϕ∧Πψ⇔Π) = nlp∧nlp-eq-nlp Πϕ Πψ
    ϕ∧ψ⇔Π =     ϕ    ∧     ψ    ≡HT⟨ replace∧lhs ϕ⇔Πϕ ⟩
            NLP2F Πϕ ∧     ψ    ≡HT⟨ replace∧rhs ψ⇔Πψ ⟩
            NLP2F Πϕ ∧ NLP2F Πψ ≡HT⟨ Πϕ∧Πψ⇔Π ⟩
                  NLP2F Π       ■
  in
    Π , ϕ∧ψ⇔Π
f\∨-eq-nlp (f\∨ (ϕ ⇒ ψ) (ϕp , ψp)) =
  let
    (Πϕ , ϕ⇔Πϕ) = f\∨-eq-nlp (f\∨ ϕ ϕp)
    (Πψ , ψ⇔Πψ) = f\∨-eq-nlp (f\∨ ψ ψp)
    (Π , Πϕ⇒Πψ⇔Π) = nlp⇒nlp-eq-nlp Πϕ Πψ
    ϕ⇒ψ⇔Π =     ϕ    ⇒     ψ    ≡HT⟨ replace⇒lhs ϕ⇔Πϕ ⟩
            NLP2F Πϕ ⇒     ψ    ≡HT⟨ replace⇒rhs ψ⇔Πψ ⟩
            NLP2F Πϕ ⇒ NLP2F Πψ ≡HT⟨ Πϕ⇒Πψ⇔Π ⟩
                  NLP2F Π       ■
  in
    Π , ϕ⇒ψ⇔Π

-- for every formula ϕ there exists a nested logic program Π s.t. ϕ ⇔ Π
f-eq-nlp : (ϕ : F) → Σ NLP (λ Π → ϕ ≡HT (NLP2F Π))
f-eq-nlp f =
  let
    -- convert to formula f' without disjunction
    (f' , f⇔f') = F2F\∨ f
    -- convert f' to a nested logic program
    (Π , f'⇔Π) = f\∨-eq-nlp f'
  in
    Π , trans⇔ f⇔f' f'⇔Π

-- for every theory Γ there exists nested logic program Π s.t. Γ ⇔ Π
th-eq-nlp : (Γ : Th) → Σ NLP (λ Π → (Th2F Γ) ≡HT (NLP2F Π))
-- use the single formula case by converting the theory to a conjunction
th-eq-nlp Γ = f-eq-nlp (Th2F Γ)

-- the disjunction of two nested logic programs is a nested logic program ------
nlp∨nlp-eq-nlp : (lp1 lp2 : NLP) → Σ NLP (λ lp →
                 (NLP2F lp1 ∨ NLP2F lp2) ≡HT (NLP2F lp))
nlp∨nlp-eq-nlp Π1 Π2 = f-eq-nlp (NLP2F Π1 ∨ NLP2F Π2)
