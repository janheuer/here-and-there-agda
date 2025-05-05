module Classical.Interpretation where

open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Binary.PropositionalEquality using (sym ; trans ; cong)
open import Agda.Builtin.Unit renaming (⊤ to Unit) using (tt)
open import Data.Bool renaming (Bool to 𝔹) using (true ; false)
open import Data.Bool.Properties renaming (_≟_ to _≡𝔹?_) using ()
open import Data.List using (List ; [] ; _∷_ ; _++_ ; foldr)
open import Data.Product renaming (proj₁ to p1 ; proj₂ to p2) using (_×_ ; _,_ ; Σ-syntax)
open import Data.Sum renaming (inj₁ to inl ; inj₂ to inr) using (_⊎_ ; [_,_])
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim) using ()

open import Classical.Base
open import Classical.Language
open import Formula.Decidable

-- interpretations as a formula
-- if we have a finite interpretation i (in the sense that finitely many atoms are true)
-- we can turn the interpretation i into a formula f with the following properties:
-- i ⊧C f,
-- i is the minimal model of f, i.e. for all j ⊆ i if j ⊧C f then i ≡ j
-- note that the latter only holds in the case that at least one atom is true in i
-- in general an interpretation is not finite
-- however if we restrict any interpretation to a language it is finite
finite-IPC : IPC → Set
finite-IPC i = Σ[ (j , l) ∈ IPC × Lang ] i ≡ (j |L l)

fin-non-empty-IPC : IPC → Set
fin-non-empty-IPC i = Σ[ l ∈ Lang ] ((a : Var) → (a ∈-L l → i a ≡ true) × (i a ≡ true → a ∈-L l)) × (Σ[ a ∈ Var ] a ∈-L l)

IPC-not-empty : IPC → Set
IPC-not-empty i = Σ[ a ∈ Var ] i a ≡ true

Lang-not-empty : Lang → Set
Lang-not-empty l = Σ[ a ∈ Var ] a ∈-L l

isLiteral : F → Set
isLiteral (V a) = Unit
isLiteral((V a) ⇒ ⊥) = Unit
isLiteral _ = Ø

Literal : Set
Literal = Σ[ f ∈ F ] isLiteral f

isEmptyConjunction : F → Set
isEmptyConjunction (⊥ ⇒ ⊥) = Unit
isEmptyConjunction _ = Ø

EmptyConjunction : Set
EmptyConjunction = Σ[ f ∈ F ] isEmptyConjunction f

isLiteralConjunction : F → Set
isLiteralConjunction (f ∧ g) = (isLiteralConjunction f) × (isLiteralConjunction g)
isLiteralConjunction f = isEmptyConjunction f ⊎ isLiteral f

LiteralConjunction : Set
LiteralConjunction = Σ[ f ∈ F ] isLiteralConjunction f

postulate IPC-ext : {i j : IPC} → ((a : Var) → (i a ≡ j a)) → i ≡ j

i⊆j-and-j⊆i-imp-i≡j : {i j : IPC} → i ⊆ j → j ⊆ i → i ≡ j
i⊆j-and-j⊆i-imp-i≡j {i} {j} i⊆j j⊆i = IPC-ext x
  where
    x : (a : Var) → i a ≡ j a
    x a with i a ≡𝔹? true
    ... | yes ia≡true = eq
      where
        ja≡true = i⊆j a ia≡true
        eq = trans ia≡true (sym ja≡true)
    ... | no ia≢true with j a ≡𝔹? true
    x a | no ia≢true | yes ja≡true = Ø-elim (ia≢true (j⊆i a ja≡true))
    x a | no ia≢true | no ja≢true = eq
      where
        ≢true-imp-≡false : (b : 𝔹) → (b ≡ true → Ø) → b ≡ false
        ≢true-imp-≡false false b≢true = refl
        ≢true-imp-≡false true b≢true = Ø-elim (b≢true refl)
        ia≡false = ≢true-imp-≡false (i a) ia≢true
        ja≡false = ≢true-imp-≡false (j a) ja≢true
        eq = trans ia≡false (sym ja≡false)

lang-eq : (l1 l2 : Lang) → (i : IPC) → l1 ≡ l2 → (i |L l1) ≡ (i |L l2)
lang-eq l1 l1 i refl = refl

list-eq : (a b : Var) → a ≡ b → (a ∷ []) ≡ (b ∷ [])
list-eq a b = cong (_∷ [])

fin-IPC-to-LitCon : (i : IPC) → fin-non-empty-IPC i → Σ[ (f , fisLitCon) ∈ LiteralConjunction ] (i ⊧C f) × ((j : IPC) → (j ⊆ i) → (j ⊧C f) → i ≡ j)
fin-IPC-to-LitCon i (a ∷ [] , fin , non-empty) = (f , fisLitCon) , (i⊧f , i-min)
  where
    f = V a
    fisLitCon = inr tt
    i⊧f = (p1 (fin a)) (inl refl)
    i-min : (j : IPC) → (j ⊆ i) → (j ⊧C f) → i ≡ j
    i-min j j⊆i j⊧f = proof
      where
        i⊆j : i ⊆ j
        i⊆j b ib≡true = jb≡true
          where
            fun = p2 (fin b)
            b≡a : b ≡ a
            b≡a with fun ib≡true
            ... | inl b≡a = b≡a
            fun2 : (c d : Var) → (h : IPC) → c ≡ d → h c ≡ h d
            fun2 c c h refl = refl
            fun3 : (c d : 𝔹) → c ≡ d → c ≡ true → d ≡ true
            fun3 c c refl c≡true = c≡true
            jb≡true = fun3 (j a) (j b) (fun2 a b j (sym b≡a)) j⊧f
        proof = i⊆j-and-j⊆i-imp-i≡j i⊆j j⊆i
fin-IPC-to-LitCon i (a ∷ x ∷ l , fin , non-empty) = proof
  where
    i|a = i |L (a ∷ [])
    i|a-fin-1 : (x : Var) → (x ∈-L (a ∷ [])) → i|a x ≡ true
    i|a-fin-1 x (inl x≡a) = i|ax≡true
      where
        ix≡true = (p1 (fin x)) (inl x≡a)
        i|xx≡true = i⊧Cf-imp-i|f⊧Cf (V x) i ix≡true
        eq : (i |F (V x)) ≡ i|a
        eq1 : (i |F (V x)) ≡ (i |L (x ∷ []))
        eq1 = refl
        eq = trans eq1 (lang-eq (x ∷ []) (a ∷ []) i (list-eq x a x≡a))
        i|ax≡true = trans (cong (λ f → f x) (sym eq)) i|xx≡true
    i|a-fin-2 : (x : Var) → i|a x ≡ true → x ∈-L (a ∷ [])
    i|a-fin-2 = {!!}
    i|a-fin : ((x : Var) → (x ∈-L (a ∷ []) → i|a x ≡ true) × (i|a x ≡ true → x ∈-L (a ∷ [])))
    i|a-fin x = i|a-fin-1 x , i|a-fin-2 x
    i|a-non-empty : Σ[ x ∈ Var ] x ∈-L (a ∷ [])
    i|a-non-empty = a , (inl refl)
    base = fin-IPC-to-LitCon i|a (a ∷ [] , i|a-fin , i|a-non-empty)

    i|x,l-non-empty : Σ[ z ∈ Var ] z ∈-L (x ∷ l)
    i|x,l-non-empty = x , (inl refl)
    rec = fin-IPC-to-LitCon (i |L (x ∷ l)) (x ∷ l , {!!} , i|x,l-non-empty)

    f = p1 (p1 base)
    g = p1 (p1 rec)
    fisLitCon = p2 (p1 base)
    gisLitCon = p2 (p1 base)

    proof = ((f ∧ g) , ({!fisLitCon!} , {!!})) , {!!}

new : (i : IPC) → (l : Lang) → IPC-not-empty (i |L l) → Σ[ (f , fisLitCon) ∈ LiteralConjunction ] ((i |L l) ⊧C f) × ((j : IPC) → (j ⊆ (i |L l)) → (j ⊧C f) → j ≡ (i |L l))
new i l@(a ∷ as) i|l≢Ø  with i a
... | true = {!!}
... | false = (f , fisLitCon) , (i|l⊧f , i|l-min)
  where
    v = p1 i|l≢Ø
    iv≡true = p2 i|l≢Ø
    i|as≢Ø : IPC-not-empty (i |L as)
    i|as≢Ø with a ≡Var? v
    ... | yes a≡v = {!!}
    ... | no a≢v = v , {!p2 i|l≢Ø!}
    x = new i as {!!}
    f = {!!}
    fisLitCon = {!!}
    i|l⊧f = {!!}
    i|l-min = {!!}

IPC-to-F : (i : IPC) → finite-IPC i → F
IPC-to-F i ((j , l) , i≡j|l) = f
  where
    conjoin-if-true : Var → F → F
    conjoin-if-true a ϕ with i a
    ... | true = (V a) ∧ ϕ
    ... | false = ϕ

    f = foldr conjoin-if-true ⊤ l

i|l-to-LitCon : IPC → Lang → LiteralConjunction
i|l-to-LitCon i [] = ⊤ , (inl tt)
i|l-to-LitCon i (a ∷ as) with i a
... | true = f , fisLitCon
  where
    rec = i|l-to-LitCon i as
    g = p1 rec
    gisLitCon = p2 rec
    f = (V a) ∧ g
    fisLitCon = (inr tt) , gisLitCon
... | false = i|l-to-LitCon i as

i|f-to-LitCon : IPC → F → LiteralConjunction
i|f-to-LitCon i f = i|l-to-LitCon i (lang-of f)

helper : (i : IPC) → (a : Var) → Σ[ b ∈ 𝔹 ] (i a ≡ b)
helper i a = (i a) , refl

temp1 : (i : IPC) → (l : Lang) → (i |L l) ⊧C (p1 (i|l-to-LitCon i l))
temp1 i [] = proof
  where
    eq : p1 (i|l-to-LitCon i []) ≡ ⊤
    eq = refl
    proof : i ⊧C ⊤
    proof = λ i⊧C⊥ → i⊧C⊥
temp1 i l@(a ∷ as) with helper i a
... | (true , ia≡true) = proof
  where
    g = p1 (i|l-to-LitCon i as)
    f = (V a) ∧ g
    eq : f ≡ p1 (i|l-to-LitCon i l)
    eq with i a
    ... | false = Ø-elim (x ia≡true)
      where
        x : (false ≡ true) → Ø
        x ()
    ... | true = refl
    i|l⊧a : (i |L l) ⊧C (V a)
    i|l⊧a with ∈-L-dec a l
    ... | inl a∈l = ia≡true
    ... | inr a∉l = Ø-elim (a∉l (inl refl))
    i|as⊧g : (i |L as) ⊧C g
    i|as⊧g = temp1 i as
    i|g⊧g : ((i |L as) |F g) ⊧C g
    i|g⊧g = i⊧Cf-imp-i|f⊧Cf g (i |L as) i|as⊧g
    g⊆l : (lang-of g) ⊆-L l
    g⊆l = {!!}
    i|l⊧g : (i |L l) ⊧C g
    i|l⊧g = i|f⊧Cf-imp-i|f+⊧Cf g i l g⊆l {!!}
    proof : (i |L l) ⊧C p1 (i|l-to-LitCon i l)
    proof = {!!}
... | (false , ia≡false) = {!!}

-- IPC-to-F-model : (i : IPC) → (fin : finite-IPC i) → i ⊧C (IPC-to-F i fin)
-- IPC-to-F-model i ((j , []) , i≡j|l) = i⊧C⊤
--   where
--     i⊧C⊤ : i ⊧C (⊥ ⇒ ⊥)
--     i⊧C⊤ ()
-- IPC-to-F-model i ((j , a ∷ as) , i≡j|l) with i a
-- ... | false = {!!}
-- ... | true = {!!}

-- IPC-to-F-min : (i : IPC) → (l : Lang) → not-all-false (i |L l) →  (j : IPC) → (j ⊆ i) → (j ⊧C (IPC-to-F i l)) → i ≡ j
-- IPC-to-F-min = {!!}
