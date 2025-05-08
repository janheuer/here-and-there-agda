module AnswerSet.LogicProgram where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Unit using (tt)
open import Data.List using (List ; [] ; _∷_)
open import Data.Sum renaming (inj₁ to inl ; inj₂ to inr) using (_⊎_)
open import Data.Product renaming (proj₁ to p1 ; proj₂ to p2) using (_×_ ; _,_)
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim) using ()

open import Formula public
open import Classical public
open import HereAndThere public
open import Equilibrium public
open import Formula.LogicPrograms public

-- we start by defining the positive/negative body/head of a rule
-- first, the positive body
positive-body : Rule → EmptyBody ⊎ LiteralConjunction
positive-body ((⊥ ⇒ ⊥) ⇒ h , _) = inl ((⊥ ⇒ ⊥) , tt)
positive-body (V a ⇒ h , _) = inr (V a , tt)
positive-body ((V a ⇒ ⊥) ⇒ h , _) = inl ((⊥ ⇒ ⊥) , tt)
positive-body ((f ∧ g) ⇒ h , (inr (fisBody , gisBody) , hisHead)) with positive-body (f ⇒ h , (inr fisBody , hisHead)) | positive-body (g ⇒ h , (inr gisBody , hisHead))
... | inl _ | inl _ = inl ((⊥ ⇒ ⊥) , tt)
... | inl _ | inr pos-g = inr pos-g
... | inr pos-f | inl _ = inr pos-f
... | inr pos-f | inr pos-g = inr (ϕ , ϕisLitCon)
  where
    f+ = p1 pos-f
    f+isLitCon = p2 pos-f
    g+ = p1 pos-g
    g+isLitCon = p2 pos-g
    ϕ = f+ ∧ g+
    ϕisLitCon = f+isLitCon , g+isLitCon
-- absurd
positive-body (⊥ ⇒ g , inl () , snd)
positive-body (⊥ ⇒ g , inr () , snd)
positive-body ((f ∧ f₁) ⇒ g , inl () , snd)
positive-body ((f ∨ f₁) ⇒ g , inl () , snd)
positive-body ((f ∨ f₁) ⇒ g , inr () , snd)
positive-body ((⊥ ⇒ V x₁) ⇒ h , inl () , snd)
positive-body ((⊥ ⇒ (g ∧ g₁)) ⇒ h , inl () , snd)
positive-body ((⊥ ⇒ (g ∨ g₁)) ⇒ h , inl () , snd)
positive-body ((⊥ ⇒ g ⇒ g₁) ⇒ h , inl () , snd)
positive-body ((V x ⇒ V x₁) ⇒ h , inl () , snd)
positive-body ((V x ⇒ V x₁) ⇒ h , inr () , snd)
positive-body ((V x ⇒ (g ∧ g₁)) ⇒ h , inl () , snd)
positive-body ((V x ⇒ (g ∧ g₁)) ⇒ h , inr () , snd)
positive-body ((V x ⇒ (g ∨ g₁)) ⇒ h , inl () , snd)
positive-body ((V x ⇒ (g ∨ g₁)) ⇒ h , inr () , snd)
positive-body ((V x ⇒ g ⇒ g₁) ⇒ h , inl () , snd)
positive-body ((V x ⇒ g ⇒ g₁) ⇒ h , inr () , snd)
positive-body (((f ∧ f₁) ⇒ g) ⇒ h , inl () , snd)
positive-body (((f ∧ f₁) ⇒ g) ⇒ h , inr () , snd)
positive-body (((f ∨ f₁) ⇒ g) ⇒ h , inl () , snd)
positive-body (((f ∨ f₁) ⇒ g) ⇒ h , inr () , snd)
positive-body (((f ⇒ f₁) ⇒ g) ⇒ h , inl () , snd)
positive-body (((f ⇒ f₁) ⇒ g) ⇒ h , inr () , snd)
-- analogously the negative body
negative-body : Rule → EmptyBody ⊎ LiteralConjunction
negative-body ((⊥ ⇒ ⊥) ⇒ h , _) = inl ((⊥ ⇒ ⊥) , tt)
negative-body (V a ⇒ h , _) = inl ((⊥ ⇒ ⊥) , tt)
negative-body ((V a ⇒ ⊥) ⇒ h , _) = inr ((V a ⇒ ⊥) , tt)
negative-body ((f ∧ g) ⇒ h , (inr (fisBody , gisBody) , hisHead)) with negative-body (f ⇒ h , (inr fisBody , hisHead)) | negative-body (g ⇒ h , (inr gisBody , hisHead))
... | inl _ | inl _ = inl ((⊥ ⇒ ⊥) , tt)
... | inl _ | inr neg-g = inr neg-g
... | inr neg-f | inl _ = inr neg-f
... | inr neg-f | inr neg-g = inr (ϕ , ϕisLitCon)
  where
    f- = p1 neg-f
    f-isLitCon = p2 neg-f
    g- = p1 neg-g
    g-isLitCon = p2 neg-g
    ϕ = f- ∧ g-
    ϕisLitCon = f-isLitCon , g-isLitCon
-- absurd
negative-body (⊥ ⇒ g , inl () , snd)
negative-body (⊥ ⇒ g , inr () , snd)
negative-body ((f ∧ f₁) ⇒ g , inl () , snd)
negative-body ((f ∨ f₁) ⇒ g , inl () , snd)
negative-body ((f ∨ f₁) ⇒ g , inr () , snd)
negative-body ((⊥ ⇒ V x₁) ⇒ h , inl () , snd)
negative-body ((⊥ ⇒ (g ∧ g₁)) ⇒ h , inl () , snd)
negative-body ((⊥ ⇒ (g ∨ g₁)) ⇒ h , inl () , snd)
negative-body ((⊥ ⇒ g ⇒ g₁) ⇒ h , inl () , snd)
negative-body ((V x ⇒ V x₁) ⇒ h , inl () , snd)
negative-body ((V x ⇒ V x₁) ⇒ h , inr () , snd)
negative-body ((V x ⇒ (g ∧ g₁)) ⇒ h , inl () , snd)
negative-body ((V x ⇒ (g ∧ g₁)) ⇒ h , inr () , snd)
negative-body ((V x ⇒ (g ∨ g₁)) ⇒ h , inl () , snd)
negative-body ((V x ⇒ (g ∨ g₁)) ⇒ h , inr () , snd)
negative-body ((V x ⇒ g ⇒ g₁) ⇒ h , inl () , snd)
negative-body ((V x ⇒ g ⇒ g₁) ⇒ h , inr () , snd)
negative-body (((f ∧ f₁) ⇒ g) ⇒ h , inl () , snd)
negative-body (((f ∧ f₁) ⇒ g) ⇒ h , inr () , snd)
negative-body (((f ∨ f₁) ⇒ g) ⇒ h , inl () , snd)
negative-body (((f ∨ f₁) ⇒ g) ⇒ h , inr () , snd)
negative-body (((f ⇒ f₁) ⇒ g) ⇒ h , inl () , snd)
negative-body (((f ⇒ f₁) ⇒ g) ⇒ h , inr () , snd)
-- positive head
positive-head : Rule → EmptyHead ⊎ LiteralDisjunction
positive-head (b ⇒ ⊥ , _) = inl (⊥ , tt)
positive-head (b ⇒ V a , _) = inr (V a , tt)
positive-head (b ⇒ (V a ⇒ ⊥) , _) = inl (⊥ , tt)
positive-head (b ⇒ (f ∨ g) , (bisBody , inr (fisHead , gisHead))) with positive-head (b ⇒ f , (bisBody , inr fisHead)) | positive-head (b ⇒ g , (bisBody , inr gisHead))
... | inl _ | inl _ = inl (⊥ , tt)
... | inl _ | inr pos-g = inr pos-g
... | inr pos-f | inl _ = inr pos-f
... | inr pos-f | inr pos-g = inr (ϕ , ϕisLitDis)
  where
    f+ = p1 pos-f
    f+isLitDis = p2 pos-f
    g+ = p1 pos-g
    g+isLitDis = p2 pos-g
    ϕ = f+ ∨ g+
    ϕisLitDis = f+isLitDis , g+isLitDis
positive-head (b ⇒ (h ∧ h₁) , fst , inl ())
positive-head (b ⇒ (h ∧ h₁) , fst , inr ())
positive-head (b ⇒ (⊥ ∨ h₁) , fst , inl ())
positive-head (b ⇒ (V x ∨ ⊥) , fst , inl ())
positive-head (b ⇒ (V x ∨ h₁ ∧ h₂) , fst , inl ())
positive-head (b ⇒ (V x ∨ h₁ ∨ h₂) , fst , inl ())
positive-head (b ⇒ (V x ∨ h₁ ⇒ h₂) , fst , inl ())
positive-head (b ⇒ (h ∧ h₂ ∨ h₁) , fst , inl ())
positive-head (b ⇒ ((h ∨ h₂) ∨ h₁) , fst , inl ())
positive-head (b ⇒ (h ⇒ h₂ ∨ h₁) , fst , inl ())
positive-head (b ⇒ ⊥ ⇒ ⊥ , fst , inr ())
positive-head (b ⇒ (h ∧ h₁) ⇒ ⊥ , fst , inr ())
positive-head (b ⇒ (h ∨ h₁) ⇒ ⊥ , fst , inr ())
positive-head (b ⇒ (h ⇒ h₁) ⇒ ⊥ , fst , inr ())
positive-head (b ⇒ ⊥ ⇒ V x , fst , inr ())
positive-head (b ⇒ V x₁ ⇒ V x , fst , inr ())
positive-head (b ⇒ (h ∧ h₁) ⇒ V x , fst , inr ())
positive-head (b ⇒ (h ∨ h₁) ⇒ V x , fst , inr ())
positive-head (b ⇒ (h ⇒ h₁) ⇒ V x , fst , inr ())
positive-head (b ⇒ ⊥ ⇒ (h₁ ∧ h₂) , fst , inr ())
positive-head (b ⇒ V x ⇒ (h₁ ∧ h₂) , fst , inr ())
positive-head (b ⇒ (h ∧ h₃) ⇒ (h₁ ∧ h₂) , fst , inr ())
positive-head (b ⇒ (h ∨ h₃) ⇒ (h₁ ∧ h₂) , fst , inr ())
positive-head (b ⇒ (h ⇒ h₃) ⇒ (h₁ ∧ h₂) , fst , inr ())
positive-head (b ⇒ ⊥ ⇒ (h₁ ∨ h₂) , fst , inr ())
positive-head (b ⇒ V x ⇒ (h₁ ∨ h₂) , fst , inr ())
positive-head (b ⇒ (h ∧ h₃) ⇒ (h₁ ∨ h₂) , fst , inr ())
positive-head (b ⇒ (h ∨ h₃) ⇒ (h₁ ∨ h₂) , fst , inr ())
positive-head (b ⇒ (h ⇒ h₃) ⇒ (h₁ ∨ h₂) , fst , inr ())
positive-head (b ⇒ ⊥ ⇒ h₁ ⇒ h₂ , fst , inr ())
positive-head (b ⇒ V x ⇒ h₁ ⇒ h₂ , fst , inr ())
positive-head (b ⇒ (h ∧ h₃) ⇒ h₁ ⇒ h₂ , fst , inr ())
positive-head (b ⇒ (h ∨ h₃) ⇒ h₁ ⇒ h₂ , fst , inr ())
positive-head (b ⇒ (h ⇒ h₃) ⇒ h₁ ⇒ h₂ , fst , inr ())
-- negative head
negative-head : Rule → EmptyHead ⊎ LiteralDisjunction
negative-head (b ⇒ ⊥ , _) = inl (⊥ , tt)
negative-head (b ⇒ V a , _) = inl (⊥ , tt)
negative-head (b ⇒ (V a ⇒ ⊥) , _) = inr ((V a ⇒ ⊥) , tt)
negative-head (b ⇒ (f ∨ g) , (bisBody , inr (fisHead , gisHead))) with negative-head (b ⇒ f , (bisBody , inr fisHead)) | negative-head (b ⇒ g , (bisBody , inr gisHead))
... | inl _ | inl _ = inl (⊥ , tt)
... | inl _ | inr neg-g = inr neg-g
... | inr neg-f | inl _ = inr neg-f
... | inr neg-f | inr neg-g = inr (ϕ , ϕisLitDis)
  where
    f- = p1 neg-f
    f-isLitDis = p2 neg-f
    g- = p1 neg-g
    g-isLitDis = p2 neg-g
    ϕ = f- ∨ g-
    ϕisLitDis = f-isLitDis , g-isLitDis
negative-head (b ⇒ (h ∧ h₁) , fst , inl ())
negative-head (b ⇒ (h ∧ h₁) , fst , inr ())
negative-head (b ⇒ ⊥ ⇒ ⊥ , fst , inr ())
negative-head (b ⇒ (h ∧ h₁) ⇒ ⊥ , fst , inr ())
negative-head (b ⇒ (h ∨ h₁) ⇒ ⊥ , fst , inr ())
negative-head (b ⇒ (h ⇒ h₁) ⇒ ⊥ , fst , inr ())
negative-head (b ⇒ ⊥ ⇒ V x , fst , inr ())
negative-head (b ⇒ V x₁ ⇒ V x , fst , inr ())
negative-head (b ⇒ (h ∧ h₁) ⇒ V x , fst , inr ())
negative-head (b ⇒ (h ∨ h₁) ⇒ V x , fst , inr ())
negative-head (b ⇒ (h ⇒ h₁) ⇒ V x , fst , inr ())
negative-head (b ⇒ ⊥ ⇒ (h₁ ∧ h₂) , fst , inr ())
negative-head (b ⇒ V x ⇒ (h₁ ∧ h₂) , fst , inr ())
negative-head (b ⇒ (h ∧ h₃) ⇒ (h₁ ∧ h₂) , fst , inr ())
negative-head (b ⇒ (h ∨ h₃) ⇒ (h₁ ∧ h₂) , fst , inr ())
negative-head (b ⇒ (h ⇒ h₃) ⇒ (h₁ ∧ h₂) , fst , inr ())
negative-head (b ⇒ ⊥ ⇒ (h₁ ∨ h₂) , fst , inr ())
negative-head (b ⇒ V x ⇒ (h₁ ∨ h₂) , fst , inr ())
negative-head (b ⇒ (h ∧ h₃) ⇒ (h₁ ∨ h₂) , fst , inr ())
negative-head (b ⇒ (h ∨ h₃) ⇒ (h₁ ∨ h₂) , fst , inr ())
negative-head (b ⇒ (h ⇒ h₃) ⇒ (h₁ ∨ h₂) , fst , inr ())
negative-head (b ⇒ ⊥ ⇒ h₁ ⇒ h₂ , fst , inr ())
negative-head (b ⇒ V x ⇒ h₁ ⇒ h₂ , fst , inr ())
negative-head (b ⇒ (h ∧ h₃) ⇒ h₁ ⇒ h₂ , fst , inr ())
negative-head (b ⇒ (h ∨ h₃) ⇒ h₁ ⇒ h₂ , fst , inr ())
negative-head (b ⇒ (h ⇒ h₃) ⇒ h₁ ⇒ h₂ , fst , inr ())

rule-reduct : Rule → IPC → Rule
rule-reduct r i = reduct-r
  where
    b+ = positive-body r
    b- = negative-body r
    h+ = positive-head r
    h- = negative-head r

    reduct-r = {!!}
