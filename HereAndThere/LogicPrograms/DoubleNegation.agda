module HereAndThere.LogicPrograms.DoubleNegation where

open import Data.Product using (_×_ ; _,_ ; <_,_>)
                         renaming (proj₁ to p1 ; proj₂ to p2)
open import Data.Sum using (_⊎_ ; [_,_]) renaming (inj₁ to inl ; inj₂ to inr)

open import HereAndThere.Base
open import HereAndThere.LogicPrograms.Nested
open import Formula.LogicPrograms
open import Formula.LogicPrograms.Nested
open import Formula.LogicPrograms.DoubleNegation

-- removal of disjunction in body of implications ------------------------------
-- LifschitzEtAl1999 proposition 6 (ii)
-- (f ∨ g) ⇒ j is equivalent to (f ⇒ j) ∧ (g ⇒ j)
rem∨body : (f g j : F) → ((f ∨ g) ⇒ j) ≡HT ((f ⇒ j) ∧ (g ⇒ j))
rem∨body f g j i@(IHT h t p) = (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)
  where
    liftinl : {A B C : Set} → ((A ⊎ B) → C) → A → C
    liftinl f a = f (inl a)

    liftinr : {A B C : Set} → ((A ⊎ B) → C) → B → C
    liftinr f b = f (inr b)

    lift : {A B C : Set} → ((A ⊎ B) → C) → (A → C) × (B → C)
    lift f = liftinl f , liftinr f

    proof⇒C : t ⊧C ((f ∨ g) ⇒ j) → t ⊧C ((f ⇒ j) ∧ (g ⇒ j))
    proof⇒C = lift

    proof⇒HT : i ⊧HT ((f ∨ g) ⇒ j) → i ⊧HT ((f ⇒ j) ∧ (g ⇒ j))
    proof⇒HT (⊧HTf∨g⇒j , ⊧Cf∨g⇒j) =
      (liftinl ⊧HTf∨g⇒j , (p1 (proof⇒C ⊧Cf∨g⇒j))) ,
      (liftinr ⊧HTf∨g⇒j , (p2 (proof⇒C ⊧Cf∨g⇒j)))

    proof⇐C : t ⊧C ((f ⇒ j) ∧ (g ⇒ j)) → t ⊧C ((f ∨ g) ⇒ j)
    proof⇐C (⊧f⇒j , ⊧g⇒j) = [ ⊧f⇒j , ⊧g⇒j ]

    proof⇐HT : i ⊧HT ((f ⇒ j) ∧ (g ⇒ j)) → i ⊧HT ((f ∨ g) ⇒ j)
    proof⇐HT ((⊧HTf⇒j , ⊧Cf⇒j) , (⊧HTg⇒j , ⊧Cg⇒j)) =
      [ ⊧HTf⇒j , ⊧HTg⇒j ] ,
      proof⇐C (⊧Cf⇒j , ⊧Cg⇒j)

-- removal of conjucntion in head of implications ------------------------------
-- LifschitzEtAl1999 proposition 6 (i)
-- f ⇒ (g ∧ j) is equivalent to (f ⇒ g) ∧ (f ⇒ j)
rem∧head : (f g j : F) → (f ⇒ (g ∧ j)) ≡HT ((f ⇒ g) ∧ (f ⇒ j))
rem∧head f g j i@(IHT h t p) = (proof⇒HT , proof⇒C) , (proof⇐HT , proof⇐C)
  where
    liftp1 : {A B C : Set} → (A → (B × C)) → A → B
    liftp1 f a = p1 (f a)

    liftp2 : {A B C : Set} → (A → (B × C)) → A → C
    liftp2 f a = p2 (f a)

    lift : {A B C : Set} → (A → (B × C)) → ((A → B) × (A → C))
    lift f = liftp1 f , liftp2 f

    proof⇒C : t ⊧C (f ⇒ (g ∧ j)) → t ⊧C ((f ⇒ g) ∧ (f ⇒ j))
    proof⇒C = lift

    proof⇒HT : i ⊧HT (f ⇒ (g ∧ j)) → i ⊧HT ((f ⇒ g) ∧ (f ⇒ j))
    proof⇒HT (⊧HTf⇒g∧j , ⊧Cf⇒g∧j) =
      (liftp1 ⊧HTf⇒g∧j , (p1 (proof⇒C ⊧Cf⇒g∧j))) ,
      (liftp2 ⊧HTf⇒g∧j , (p2 (proof⇒C ⊧Cf⇒g∧j)))

    proof⇐C : t ⊧C ((f ⇒ g) ∧ (f ⇒ j)) → t ⊧C (f ⇒ (g ∧ j))
    proof⇐C (⊧f⇒g , ⊧f⇒j) = < ⊧f⇒g , ⊧f⇒j >

    proof⇐HT : i ⊧HT ((f ⇒ g) ∧ (f ⇒ j)) → i ⊧HT (f ⇒ (g ∧ j))
    proof⇐HT ((⊧HTf⇒g , ⊧Cf⇒g) , (⊧HTf⇒j , ⊧Cf⇒j)) =
      < ⊧HTf⇒g , ⊧HTf⇒j > ,
      proof⇐C (⊧Cf⇒g , ⊧Cf⇒j)

-- { SD ∧ .. ∧ SD ← SC ∨ .. ∨ SC }
-- { SD ← SC ∨ .. ∨ SC }
-- TODO: lemma SD ∧ .. ∧ SD ← SC ∨ .. ∨ SC is equivalent to { SD ← SC ∨ .. ∨ SC }
-- { SD ← SC }
-- TODO: lemma SD ← SC ∨ .. ∨ SC is equivalent to { SD ← SC }
