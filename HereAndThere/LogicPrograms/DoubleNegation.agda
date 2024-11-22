module HereAndThere.LogicPrograms.DoubleNegation where

open import Data.Product using (_,_)
                         renaming (proj₁ to p1 ; proj₂ to p2)
open import Data.Sum using ([_,_]) renaming (inj₁ to inl ; inj₂ to inr)

open import HereAndThere.Base
open import HereAndThere.LogicPrograms.Nested
open import Formula.LogicPrograms
open import Formula.LogicPrograms.Nested
open import Formula.LogicPrograms.DoubleNegation

-- removal of disjunction in body of implications ------------------------------
-- (f ∨ g) ⇒ j is equivalent to (f ⇒ j) ∧ (g ⇒ j)
rem∨body : (f g j : F) → ((f ∨ g) ⇒ j) ≡HT ((f ⇒ j) ∧ (g ⇒ j))
rem∨body f g j i@(IHT h t p) = (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)
  where
    proof⇒C : t ⊧C ((f ∨ g) ⇒ j) → t ⊧C ((f ⇒ j) ∧ (g ⇒ j))
    proof⇒C ⊧f∨g⇒j = (λ ⊧f → ⊧f∨g⇒j (inl ⊧f)) ,
                     (λ ⊧g → ⊧f∨g⇒j (inr ⊧g))

    proof⇒HT : i ⊧HT ((f ∨ g) ⇒ j) → i ⊧HT ((f ⇒ j) ∧ (g ⇒ j))
    proof⇒HT (⊧HTf∨g⇒j , ⊧Cf∨g⇒j) =
      ((λ ⊧HTf → ⊧HTf∨g⇒j (inl ⊧HTf)) , (p1 (proof⇒C ⊧Cf∨g⇒j))) ,
      ((λ ⊧HTg → ⊧HTf∨g⇒j (inr ⊧HTg)) , (p2 (proof⇒C ⊧Cf∨g⇒j)))

    proof⇐C : t ⊧C ((f ⇒ j) ∧ (g ⇒ j)) → t ⊧C ((f ∨ g) ⇒ j)
    proof⇐C (⊧f⇒j , ⊧g⇒j) = [ ⊧f⇒j , ⊧g⇒j ]

    proof⇐HT : i ⊧HT ((f ⇒ j) ∧ (g ⇒ j)) → i ⊧HT ((f ∨ g) ⇒ j)
    proof⇐HT ((⊧HTf⇒j , ⊧Cf⇒j) , (⊧HTg⇒j , ⊧Cg⇒j)) =
      [ ⊧HTf⇒j , ⊧HTg⇒j ] ,
      proof⇐C (⊧Cf⇒j , ⊧Cg⇒j)

-- removal of conjucntion in head of implications ------------------------------
-- f ⇒ (g ∧ j) is equivalent to (f ⇒ g) ∧ (f ⇒ j)
rem∧head : (f g j : F) → (f ⇒ (g ∧ j)) ≡HT ((f ⇒ g) ∧ (f ⇒ j))
rem∧head f g j i@(IHT h t p) = (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)
  where
    proof⇒C : t ⊧C (f ⇒ (g ∧ j)) → t ⊧C ((f ⇒ g) ∧ (f ⇒ j))
    proof⇒C ⊧f⇒g∧j = (λ ⊧f → p1 (⊧f⇒g∧j ⊧f)) ,
                     (λ ⊧f → p2 (⊧f⇒g∧j ⊧f))

    proof⇒HT : i ⊧HT (f ⇒ (g ∧ j)) → i ⊧HT ((f ⇒ g) ∧ (f ⇒ j))
    proof⇒HT (⊧HTf⇒g∧j , ⊧Cf⇒g∧j) =
      ((λ ⊧HTf → p1 (⊧HTf⇒g∧j ⊧HTf)) , (p1 (proof⇒C ⊧Cf⇒g∧j))) ,
      ((λ ⊧HTf → p2 (⊧HTf⇒g∧j ⊧HTf)) , (p2 (proof⇒C ⊧Cf⇒g∧j)))

    proof⇐C : t ⊧C ((f ⇒ g) ∧ (f ⇒ j)) → t ⊧C (f ⇒ (g ∧ j))
    proof⇐C (⊧f⇒g , ⊧f⇒j) ⊧f = ⊧f⇒g ⊧f , ⊧f⇒j ⊧f

    proof⇐HT : i ⊧HT ((f ⇒ g) ∧ (f ⇒ j)) → i ⊧HT (f ⇒ (g ∧ j))
    proof⇐HT ((⊧HTf⇒g , ⊧Cf⇒g) , (⊧HTf⇒j , ⊧Cf⇒j)) =
      (λ ⊧HTf → (⊧HTf⇒g ⊧HTf , ⊧HTf⇒j ⊧HTf)) ,
      proof⇐C (⊧Cf⇒g , ⊧Cf⇒j)
