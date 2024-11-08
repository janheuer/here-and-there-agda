module HereAndThere.NestedLogicPrograms where

open import Data.List using (_++_ ; map)

open import HereAndThere
open import Formula.WithoutDisjunction
open import Formula.LogicPrograms.Nested

-- the conjunction of two nested logic programs is a nested logic program ------
-- nlp ++ nlp is a nlp
NLP++NLPisNLP : ((Π1 , _) (Π2 , _) : NLP) → isNLP (Π1 ++ Π2)
NLP++NLPisNLP ([] , _) (Π2 , Π2isNLP) = Π2isNLP
NLP++NLPisNLP ((f ∷ Π1) , (fisNR , Π1isNLP)) Π2 =
  fisNR , NLP++NLPisNLP (Π1 , Π1isNLP) Π2

-- t1 ∧ t2 is equivalent to t1 ++ t2
Th∧Th-eq-Th++Th : {t1 t2 : Th} →
                  ((Th2F t1) ∧ (Th2F t2)) ≡HT Th2F (t1 ++ t2)
Th∧Th-eq-Th++Th {[]} {t2} = ⊤-lid-∧
Th∧Th-eq-Th++Th {f ∷ t1} {t2} =
  (f ∧ Th2F t1) ∧ Th2F t2 ≡HT⟨ assoc∧ ⟩
  f ∧ (Th2F t1 ∧ Th2F t2) ≡HT⟨ replace∧rhs Th∧Th-eq-Th++Th ⟩
  f ∧ Th2F (t1 ++ t2)     ■

-- for lp1, lp2 : nested logic program there exists a nested logic program lp
-- s.t. lp1 ∧ lp2 is equivalent to lp
nlp∧nlp-eq-nlp : (lp1 lp2 : NLP) → Σ[ lp ∈ NLP ]
                 ((NLP2F lp1 ∧ NLP2F lp2) ≡HT (NLP2F lp))
nlp∧nlp-eq-nlp Π1 Π2 =
  ((p1 Π1 ++ p1 Π2) , NLP++NLPisNLP Π1 Π2) , Th∧Th-eq-Th++Th

-- the implication of two nested logic programs is a nested logic program ------
-- 3 helper lemmas for proof of nlp⇒nlp-eq-nlp
-- specifically for the case where lp1 = (f ⇒ g)

-- 1) f ⇒ [t0, .., tn] is equivalent to [f ⇒ t0 , .., f ⇒ tn]
-- factor ⇒ into a theory
factor⇒Th : F → Th → Th
factor⇒Th f []      = []
factor⇒Th f (g ∷ t) = (f ⇒ g) ∷ (factor⇒Th f t)

-- factor⇒Th produces equivalent theory
factor⇒Th≡HT : (f : F) → (t : Th) →
            (f ⇒ (Th2F t)) ≡HT (Th2F (factor⇒Th f t))
factor⇒Th≡HT f [] = ⊤-rzero-⇒
factor⇒Th≡HT f (g ∷ th) =
  f ⇒ (g ∧ Th2F th)               ≡HT⟨ distr⇒∧ ⟩
  (f ⇒ g) ∧     (f ⇒ Th2F th)     ≡HT⟨ replace∧rhs (factor⇒Th≡HT f th) ⟩
  (f ⇒ g) ∧ Th2F (factor⇒Th f th) ■

-- result of factor⇒Th applied to nr and nlp is [nr ⇒ nr]
factor⇒Th:[NR⇒NR] : ((r , _) : NR) → ((lp , _) : NLP) →
                    ((f : F) → (f ∈ (factor⇒Th r lp)) →
                    (Σ[ ((ϕ , _) , (ψ , _)) ∈ (NR × NR) ] (f ≡ ϕ ⇒ ψ)))
factor⇒Th:[NR⇒NR] (r , risNR) ((f ∷ _) , (fisNR , _)) .(r ⇒ f) (inl refl) =
  ((r , risNR) , (f , fisNR)) , refl
factor⇒Th:[NR⇒NR] r ((_ ∷ Π) , (_ , ΠisNLP)) ϕ (inr ϕ∈factor⇒Π) =
  let
    ih = factor⇒Th:[NR⇒NR] r (Π , ΠisNLP)
  in
    ih ϕ ϕ∈factor⇒Π

-- 2) if t=[t0, .., tn] and f0 ⇔ t0, .., fn ⇔ tn then t ⇔ [f0, .., fn]
-- replace formulas of a theory by equivalent formulas
replaceTh : ((f : F) → Σ[ g ∈ F ] (f ≡HT g)) → Th → Th
replaceTh τ = map (λ ϕ → p1 (τ ϕ))

-- replaceTh produces an equivalent theory
replaceTh≡HT : (t : Th) → (τ : (f : F) → Σ[ g ∈ F ] (f ≡HT g)) →
            (Th2F t) ≡HT (Th2F (replaceTh τ t))
replaceTh≡HT [] τ = refl⇔
replaceTh≡HT (f ∷ fs) τ =
  let
    (g , f⇔g) = τ f
  in
    f ∧        Th2F fs        ≡HT⟨ replace∧lhs f⇔g ⟩
    g ∧        Th2F fs        ≡HT⟨ replace∧rhs (replaceTh≡HT fs τ) ⟩
    g ∧ Th2F (replaceTh τ fs) ■

-- actual replacement use in proof of lp⇒lp-eq-lp
replace[f⇒f-eq-f∧f] : (f : F) → Σ[ g ∈ F ] (f ≡HT g)
replace[f⇒f-eq-f∧f] ((ψ1 ⇒ ψ2) ⇒ (ψ3 ⇒ ψ4)) = f⇒f-eq-f∧fΣ ψ1 ψ2 ψ3 ψ4
replace[f⇒f-eq-f∧f] ψ = ψ , refl⇔

-- result of replaceTh replace[f⇒f-eq-f∧f] applied to [nr ⇒ nr] is [nr ∧ nr]
replaceTh:[NR∧NR] : (t : Th) → ((f : F) → (f ∈ t) →
                    (Σ[ ((ϕ , _) , (ψ , _)) ∈ (NR × NR) ] (f ≡ ϕ ⇒ ψ))) →
                    ((f : F) → (f ∈ (replaceTh replace[f⇒f-eq-f∧f] t)) →
                     (Σ[ ((ϕ , _) , (ψ , _)) ∈ (NR × NR) ] (f ≡ ϕ ∧ ψ)))
replaceTh:[NR∧NR] (f ∷ Γ) τ
  .(p1 (replace[f⇒f-eq-f∧f] f)) (inl refl) with τ f (inl refl)
... | (((ψ1 ⇒ ψ2) , (ψ1p , ψ2p)) , ((ψ3 ⇒ ψ4) , (ψ3p , ψ4p))) , refl =
  ((((ψ3 ∧ (ψ2 ∨ (¬ ψ1))) ⇒ ψ4) , ((ψ3p , (ψ2p , ψ1p)) , ψ4p)) ,
   ((ψ3 ⇒ (ψ4 ∨ (ψ1 ∨ (¬ ψ2)))) , (ψ3p , (ψ4p , (ψ1p , ψ2p)))) ) ,
  refl
replaceTh:[NR∧NR] (f ∷ Γ) τ ϕ (inr ϕ∈replaceΓ) =
  let
    ih = replaceTh:[NR∧NR] Γ (λ α α∈Γ → τ α (inr α∈Γ))
  in
    ih ϕ ϕ∈replaceΓ

-- 3) [f0 ∧ g0, .., fn ∧ gn] is equivalent to [f0, g0, .., fn, gn]
-- flatten conjunctions in a theory
flatten∧ : Th → Th
flatten∧ [] = []
flatten∧ ((f ∧ g) ∷ fs) = f ∷ g ∷ (flatten∧ fs)
flatten∧ (f       ∷ fs) = f ∷ (flatten∧ fs)

isNot∧ : F → Set
isNot∧ ⊥       = Unit
isNot∧ (V _)   = Unit
isNot∧ (_ ∧ _) = Ø
isNot∧ (_ ∨ _) = Unit
isNot∧ (_ ⇒ _) = Unit

-- flatten∧ produces an equivalent theory
flatten∧≡HT : (t : Th) → (Th2F t) ≡HT (Th2F (flatten∧ t))
-- helper lemma for the case that the first formula in t is not a conjunction
flatten∧≡HT-headisNot∧ : {f : F} → {isNot∧ f} → {t : Th} →
                         (Th2F (f ∷ t)) ≡HT (Th2F (flatten∧ (f ∷ t)))
flatten∧≡HT-headisNot∧ {f} {fisNot∧} {fs} =
    Th2F (f ∷ fs)            ≡HT⟨def⟩
    f ∧ Th2F fs              ≡HT⟨ replace∧rhs (flatten∧≡HT fs) ⟩
    f ∧ Th2F (flatten∧ fs)   ≡HT⟨def⟩
    Th2F (f ∷ (flatten∧ fs)) ≡HT⟨ flatten∧-headisNot∧ fisNot∧ ⟩ˢ
    Th2F (flatten∧ (f ∷ fs)) ■
  where
    flatten∧-headisNot∧ : {f : F} → (isNot∧ f) → {t : Th} →
                          Th2F (flatten∧ (f ∷ t)) ≡HT Th2F (f ∷ (flatten∧ t))
    flatten∧-headisNot∧ {⊥}     fisNot∧ {t} = refl⇔
    flatten∧-headisNot∧ {V _}   fisNot∧ {t} = refl⇔
    flatten∧-headisNot∧ {_ ∨ _} fisNot∧ {t} = refl⇔
    flatten∧-headisNot∧ {_ ⇒ _} fisNot∧ {t} = refl⇔
-- proof of flatten∧≡HT
flatten∧≡HT [] = refl⇔
flatten∧≡HT ((f ∧ g) ∷ fs) =
  Th2F ((f ∧ g) ∷ fs)            ≡HT⟨def⟩
  (f ∧ g) ∧ Th2F fs              ≡HT⟨ replace∧rhs (flatten∧≡HT fs) ⟩
  (f ∧ g) ∧ Th2F (flatten∧ fs)   ≡HT⟨ assoc∧ ⟩
  f ∧ (g ∧ Th2F (flatten∧ fs))   ≡HT⟨def⟩
  f ∧ Th2F (g ∷ (flatten∧ fs))   ≡HT⟨def⟩
  Th2F (f ∷ g ∷ (flatten∧ fs))   ≡HT⟨def⟩
  Th2F (flatten∧ ((f ∧ g) ∷ fs)) ■
flatten∧≡HT (⊥ ∷ fs)       = flatten∧≡HT-headisNot∧
flatten∧≡HT ((V a) ∷ fs)   = flatten∧≡HT-headisNot∧
flatten∧≡HT ((f ∨ g) ∷ fs) = flatten∧≡HT-headisNot∧
flatten∧≡HT ((f ⇒ g) ∷ fs) = flatten∧≡HT-headisNot∧

-- result of flatten∧ applied to [nr ∧ nr] is [nr]
flatten∧:[NR] : (t : Th) → ((f : F) → (f ∈ t) →
                (Σ[ ((ϕ , _) , (ψ , _)) ∈ (NR × NR) ] (f ≡ ϕ ∧ ψ))) →
                    ((f : F) → (f ∈ (flatten∧ t)) → (isNR f))
flatten∧:[NR] (f ∷ Γ) τ ϕ _ with τ f (inl refl)
flatten∧:[NR] (.(r1 ∧ _) ∷ Γ) τ .r1 (inl refl)
  | ((r1 , r1p) , _) , refl = r1p
flatten∧:[NR] (.(_ ∧ r2) ∷ Γ) τ .r2 (inr (inl refl))
  | (_ , (r2 , r2p)) , refl = r2p
flatten∧:[NR] (.(_ ∧ _) ∷ Γ) τ ϕ (inr (inr ϕ∈flatten∧Γ))
  | (_ , _) , refl =
  let
    ih = flatten∧:[NR] Γ (λ α α∈Γ → τ α (inr α∈Γ))
  in
    ih ϕ ϕ∈flatten∧Γ

-- given [nr] there is an equivalent nlp
[NR]2NLP : (t : Th) → ((f : F) → (f ∈ t) → (isNR f)) →
           Σ[ Π ∈ NLP ] ((Th2F t) ≡HT (NLP2F Π))
[NR]2NLP [] σ = ([] , tt) , refl⇔
[NR]2NLP (f ∷ t) σ =
  let
    ((Π' , Π'isNLP) , t⇔Π') = [NR]2NLP t (λ g g∈t → σ g (inr g∈t))
    Π = (f ∷ Π') , (σ f (inl refl) , Π'isNLP)
    f∷t⇔f∷Π = Th2F (f ∷ t) ≡HT⟨def⟩
               f ∧ Th2F t  ≡HT⟨ replace∧rhs t⇔Π' ⟩
               f ∧ Th2F Π' ≡HT⟨def⟩
                 NLP2F Π   ■
  in
    Π , f∷t⇔f∷Π

-- for lp1, lp2 : logic program there exists a nested logic program lp
-- s.t. lp1 ⇒ lp2 is equivalent to lp
-- (lemma 2)
nlp⇒nlp-eq-nlp : (lp1 lp2 : NLP) → Σ[ lp ∈ NLP ]
                 ((NLP2F lp1 ⇒ NLP2F lp2) ≡HT (NLP2F lp))
-- [] ⇒ lp2 = ⊤ ⇒ lp2 =(by ⊤-lid-⇒) lp2
nlp⇒nlp-eq-nlp ([] , tt) lp2 = lp2 , ⊤-lid-⇒
nlp⇒nlp-eq-nlp (((f ⇒ g) ∷ []) , (rp , tt)) (lp2 , lp2p) =
  let
    -- 1) (f⇒g) ⇒ [t0, .., tn] eq. Π1 = [(f⇒g) ⇒ t0, .., (f⇒g) ⇒ tn]
    --                         by factor⇒Th
    Π1 = factor⇒Th (f ⇒ g) lp2
    -- Π1 contains only implications of rules
    Π1is[NR⇒NR] = factor⇒Th:[NR⇒NR] ((f ⇒ g) , rp) (lp2 , lp2p)
    -- 2) Π1 eq. Π2 = [  ϕ0 ∧ ψ0 , ..,  ϕn ∧ ψn  ]
    --       by replaceTh with f⇒f-eq-f∧fΣ
    Π2 = replaceTh replace[f⇒f-eq-f∧f] Π1
    -- Π2 contains only conjunctions of rules
    Π2is[NR∧NR] = replaceTh:[NR∧NR] Π1 Π1is[NR⇒NR]
    -- 3) Π2 eq. Π3 = [  ϕ0 , ψ0 , ..,  ϕn , ψn  ]
    --       by flatten∧
    Π3 = flatten∧ Π2
    -- Π3 contains only rules
    Π3is[NR] = flatten∧:[NR] Π2 Π2is[NR∧NR]
    -- 4) Π3 is a nested logic programs
    (Π , Π3⇔Π) = [NR]2NLP Π3 Π3is[NR]

    proof =
      Th2F ((f ⇒ g) ∷ []) ⇒ Th2F lp2 ≡HT⟨def⟩
      ((f ⇒ g) ∧ ⊤) ⇒ Th2F lp2 ≡HT⟨ replace⇒lhs ⊤-rid-∧ ⟩
       (f ⇒ g)      ⇒ Th2F lp2 ≡HT⟨ factor⇒Th≡HT (f ⇒ g) lp2 ⟩            -- 1)
               Th2F Π1         ≡HT⟨ replaceTh≡HT Π1 replace[f⇒f-eq-f∧f] ⟩ -- 2)
               Th2F Π2         ≡HT⟨ flatten∧≡HT Π2 ⟩                      -- 3)
               Th2F Π3         ≡HT⟨ Π3⇔Π ⟩                                -- 4)
               NLP2F Π         ■
  in
    Π , proof
nlp⇒nlp-eq-nlp (((f ⇒ g) ∷ lp1) , (rp , lp1p)) (lp2 , lp2p) =
  let
    -- lp1 ⇒ lp2 is equivalent to a nested logic program Π' by induction
    (Π' , lp1⇒lp2⇔Π') = nlp⇒nlp-eq-nlp (lp1 , lp1p) (lp2 , lp2p)
    -- (f⇒g) ⇒ Π' is equivalent to a nested logic program Π by induction
    (Π , [f⇒g]⇒Π'⇔Π) = nlp⇒nlp-eq-nlp (((f ⇒ g) ∷ []) , (rp , tt)) Π'
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
f\∨-eq-nlp : ((ϕ , _) : F\∨) → Σ[ Π ∈ NLP ] (ϕ ≡HT (NLP2F Π))
f\∨-eq-nlp (⊥ , tt) =
  let
    -- Π = { ⊥. }
    Π = ((⊤ ⇒ ⊥) ∷ []) , ((tt , tt) , tt)
    ⊥⇔Π =            ⊥        ≡HT⟨ ⊤-lid-⇒ ⟩ˢ
                 ⊤ ⇒ ⊥        ≡HT⟨ ⊤-rid-∧ ⟩ˢ
                (⊤ ⇒ ⊥) ∧ ⊤   ≡HT⟨def⟩
          Th2F ((⊤ ⇒ ⊥) ∷ []) ≡HT⟨def⟩
                 NLP2F Π      ■
  in
    Π , ⊥⇔Π
f\∨-eq-nlp ((V a) , tt) =
  let
    -- Π = { a. }
    Π = ((⊤ ⇒ (V a)) ∷ []) , ((tt , tt) , tt)
    a⇔Π =             V a         ≡HT⟨ ⊤-lid-⇒ ⟩ˢ
                 ⊤ ⇒ (V a)        ≡HT⟨ ⊤-rid-∧ ⟩ˢ
                (⊤ ⇒ (V a)) ∧ ⊤   ≡HT⟨def⟩
          Th2F ((⊤ ⇒ (V a)) ∷ []) ≡HT⟨def⟩
                   NLP2F Π        ■
  in
    Π , a⇔Π
f\∨-eq-nlp ((ϕ ∧ ψ) , (ϕp , ψp)) =
  let
    (Πϕ , ϕ⇔Πϕ) = f\∨-eq-nlp (ϕ , ϕp)
    (Πψ , ψ⇔Πψ) = f\∨-eq-nlp (ψ , ψp)
    (Π , Πϕ∧Πψ⇔Π) = nlp∧nlp-eq-nlp Πϕ Πψ
    ϕ∧ψ⇔Π =     ϕ    ∧     ψ    ≡HT⟨ replace∧lhs ϕ⇔Πϕ ⟩
            NLP2F Πϕ ∧     ψ    ≡HT⟨ replace∧rhs ψ⇔Πψ ⟩
            NLP2F Πϕ ∧ NLP2F Πψ ≡HT⟨ Πϕ∧Πψ⇔Π ⟩
                  NLP2F Π       ■
  in
    Π , ϕ∧ψ⇔Π
f\∨-eq-nlp ((ϕ ⇒ ψ) , (ϕp , ψp)) =
  let
    (Πϕ , ϕ⇔Πϕ) = f\∨-eq-nlp (ϕ , ϕp)
    (Πψ , ψ⇔Πψ) = f\∨-eq-nlp (ψ , ψp)
    (Π , Πϕ⇒Πψ⇔Π) = nlp⇒nlp-eq-nlp Πϕ Πψ
    ϕ⇒ψ⇔Π =     ϕ    ⇒     ψ    ≡HT⟨ replace⇒lhs ϕ⇔Πϕ ⟩
            NLP2F Πϕ ⇒     ψ    ≡HT⟨ replace⇒rhs ψ⇔Πψ ⟩
            NLP2F Πϕ ⇒ NLP2F Πψ ≡HT⟨ Πϕ⇒Πψ⇔Π ⟩
                  NLP2F Π       ■
  in
    Π , ϕ⇒ψ⇔Π

-- for every formula ϕ there exists a nested logic program Π s.t. ϕ ⇔ Π
f-eq-nlp : (ϕ : F) → Σ[ Π ∈ NLP ] (ϕ ≡HT (NLP2F Π))
f-eq-nlp f =
  let
    -- convert to formula f' without disjunction
    (f' , f⇔f') = F2F\∨ f
    -- convert f' to a nested logic program
    (Π , f'⇔Π) = f\∨-eq-nlp f'
  in
    Π , trans⇔ f⇔f' f'⇔Π

-- for every theory Γ there exists nested logic program Π s.t. Γ ⇔ Π
th-eq-nlp : (Γ : Th) → Σ[ Π ∈ NLP ] ((Th2F Γ) ≡HT (NLP2F Π))
-- use the single formula case by converting the theory to a conjunction
th-eq-nlp Γ = f-eq-nlp (Th2F Γ)

-- the disjunction of two nested logic programs is a nested logic program ------
nlp∨nlp-eq-nlp : (lp1 lp2 : NLP) → Σ[ lp ∈ NLP ]
                 ((NLP2F lp1 ∨ NLP2F lp2) ≡HT (NLP2F lp))
nlp∨nlp-eq-nlp Π1 Π2 = f-eq-nlp (NLP2F Π1 ∨ NLP2F Π2)
