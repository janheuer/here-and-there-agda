module BoolHelper where

open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Data.Bool renaming (Bool to 𝔹 ; _∧_ to _∧𝔹_ ; _∨_ to _∨𝔹_ ;
                                not to ¬𝔹) public
open import Data.Sum.Base using (_⊎_) renaming (inj₁ to inl ; inj₂ to inr)
open import Data.Product using (_×_ ; _,_)

-- boolean implication
_⇒𝔹_ : 𝔹 → 𝔹 → 𝔹
f ⇒𝔹 g = (¬𝔹 f) ∨𝔹 g

symm : {A : Set} → {x y : A} → x ≡ y → y ≡ x
symm refl = refl

contra : {a b : 𝔹} → (a ≡ true → b ≡ true) → b ≡ false → a ≡ false
contra {false} {_}     i f = refl
contra {true}  {false} i f = symm (i refl)

-- some helper functions used in the following proofs --------------------------
×-to-∧𝔹 : {a b : 𝔹} → ((a ≡ true) × (b ≡ true)) → ((a ∧𝔹 b) ≡ true)
×-to-∧𝔹 {true} {true} _ = refl

∧𝔹-to-× : {a b : 𝔹} → ((a ∧𝔹 b) ≡ true) → ((a ≡ true) × (b ≡ true))
∧𝔹-to-× {true} {true} _ = refl , refl

⊎-to-∨𝔹 : {a b : 𝔹} → ((a ≡ true) ⊎ (b ≡ true)) → ((a ∨𝔹 b) ≡ true)
⊎-to-∨𝔹 {true}  {_}    (inl _) = refl
⊎-to-∨𝔹 {false} {true} (inr _) = refl
⊎-to-∨𝔹 {true}  {true} (inr _) = refl

∨𝔹-to-⊎ : {a b : 𝔹} → ((a ∨𝔹 b) ≡ true) → ((a ≡ true) ⊎ (b ≡ true))
∨𝔹-to-⊎ {false} p = inr p
∨𝔹-to-⊎ {true}  p = inl p

⇒𝔹-to-⊎ : {a b : 𝔹} → ((a ⇒𝔹 b) ≡ true) → ((a ≡ false) ⊎ (b ≡ true))
⇒𝔹-to-⊎ {false} {_}    p = inl refl
⇒𝔹-to-⊎ {true}  {true} p = inr refl

⊎-to-∧𝔹 : {a b : 𝔹} → ((a ≡ false) ⊎ (b ≡ false)) → ((a ∧𝔹 b) ≡ false)
⊎-to-∧𝔹 {false} {_}     (inl x) = refl
⊎-to-∧𝔹 {false} {false} (inr y) = refl
⊎-to-∧𝔹 {true}  {false} (inr y) = refl

∧𝔹-to-⊎ : {a b : 𝔹} → ((a ∧𝔹 b) ≡ false) → ((a ≡ false) ⊎ (b ≡ false))
∧𝔹-to-⊎ {false} {_}     p = inl refl
∧𝔹-to-⊎ {true}  {false} p = inr refl

×-to-∨𝔹 : {a b : 𝔹} → ((a ≡ false) × (b ≡ false)) → ((a ∨𝔹 b) ≡ false)
×-to-∨𝔹 {false} {false} p = refl

∨𝔹-to-× : {a b : 𝔹} → ((a ∨𝔹 b) ≡ false) → ((a ≡ false) × (b ≡ false))
∨𝔹-to-× {false} {false} p = refl , refl

¬𝔹-f-t : {b : 𝔹} → (b ≡ false) → ((¬𝔹 b) ≡ true)
¬𝔹-f-t {false} p = refl

¬𝔹-t-f : {b : 𝔹} → (b ≡ true) → ((¬𝔹 b) ≡ false)
¬𝔹-t-f {true} p = refl

remove-¬𝔹 : {a b : 𝔹} → ((¬𝔹 (¬𝔹 a)) ≡ b) → (a ≡ b)
remove-¬𝔹 {false} {false} p = refl
remove-¬𝔹 {true}  {true}  p = refl

→-to-⇒𝔹 : {a b : 𝔹} → (a ≡ true → b ≡ true) → a ⇒𝔹 b ≡ true
→-to-⇒𝔹 {false} {_} p = refl
→-to-⇒𝔹 {true}  {_} p = p refl

⇒𝔹-to-→ : {a b : 𝔹} → (a ⇒𝔹 b ≡ true) → a ≡ true → b ≡ true
⇒𝔹-to-→ {false} {false} p = λ x → x
⇒𝔹-to-→ {false} {true}  p = λ x → refl
⇒𝔹-to-→ {true}  {true}  p = λ x → refl
