module NatHelper where

open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Data.Nat using (ℕ ; suc ; _+_ ; _∸_ ; _≤_)
open import Data.Nat.Properties using (+-comm ; +-∸-assoc ; ≤-reflexive ;
                                       m≤n⇒m≤1+n ; ≤-step)
open import Relation.Binary.PropositionalEquality.Core using (cong ; sym)
import Relation.Binary.PropositionalEquality.Properties as Eq
open Eq.≡-Reasoning

0≡y∧x≡z⇒x≡y+z : {x y z : ℕ} → 0 ≡ y → x ≡ z → x ≡ y + z
0≡y∧x≡z⇒x≡y+z refl refl = refl

x≡y+z∧0≡y⇒x≡z : {x y z : ℕ} → x ≡ y + z → 0 ≡ y → x ≡ z
x≡y+z∧0≡y⇒x≡z refl refl = refl

1≤sn : (n : ℕ) → 1 ≤ suc n
1≤sn 0       = ≤-reflexive refl
1≤sn (suc n) = m≤n⇒m≤1+n (1≤sn n)

sn≡a+b∧sm≡a∧m≡c⇒n≡b+c : {n m a b c : ℕ} → suc n ≡ a + b → suc m ≡ a → m ≡ c →
                        n ≡ b + c
sn≡a+b∧sm≡a∧m≡c⇒n≡b+c {n} {m} {a} {b} {c} sn≡a+b sm≡a m≡c =
  n               ≡⟨⟩
  suc n ∸ 1       ≡⟨ cong (λ x → x ∸ 1) sn≡a+b ⟩
  (a + b) ∸ 1     ≡⟨ cong (λ x → x ∸ 1) (+-comm a b) ⟩
  (b + a) ∸ 1     ≡⟨ cong (λ x → (b + x) ∸ 1) (sym sm≡a) ⟩
  (b + suc m) ∸ 1 ≡⟨ +-∸-assoc b {suc m} (1≤sn m) ⟩
  b + (suc m ∸ 1) ≡⟨⟩
  b + m           ≡⟨ cong (λ x → b + x) m≡c ⟩
  b + c           ∎
