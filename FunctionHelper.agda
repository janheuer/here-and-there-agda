module FunctionHelper where

open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Data.Product using (_×_ ; _,_ ; <_,_> ; Σ-syntax)
                         renaming (proj₁ to p1 ; proj₂ to p2)
open import Data.Sum using (_⊎_ ; [_,_]) renaming (inj₁ to inl ; inj₂ to inr)

restrict-sum-inl : {A B C : Set} → ((A ⊎ B) → C) → A → C
restrict-sum-inl f a = f (inl a)

restrict-sum-inr : {A B C : Set} → ((A ⊎ B) → C) → B → C
restrict-sum-inr f b = f (inr b)

restrict-sum : {A B C : Set} → ((A ⊎ B) → C) → (A → C) × (B → C)
restrict-sum f = restrict-sum-inl f , restrict-sum-inr f

extract-product-p1 : {A B C : Set} → (A → (B × C)) → A → B
extract-product-p1 f a = p1 (f a)

extract-product-p2 : {A B C : Set} → (A → (B × C)) → A → C
extract-product-p2 f a = p2 (f a)

extract-product : {A B C : Set} → (A → (B × C)) → (A → B) × (A → C)
extract-product f = extract-product-p1 f , extract-product-p2 f
