module AnswerSet.LogicProgram where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Unit using (tt) renaming (⊤ to Unit)
open import Data.List using (List ; [] ; _∷_)
open import Data.Sum renaming (inj₁ to inl ; inj₂ to inr) using (_⊎_)
open import Data.Product renaming (proj₁ to p1 ; proj₂ to p2) using (_×_ ; _,_)
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim) using ()

open import Formula public
open import Classical public
open import HereAndThere public
open import Equilibrium public
open import Formula.LogicPrograms public
open import AnswerSet.Base public

-- we start by defining the positive/negative body/head of a rule
-- first, the positive body
positive-body : Rule → F
positive-body ((⊥ ⇒ ⊥) ⇒ h , _) = ⊥ ⇒ ⊥
positive-body (V a ⇒ h , _) = V a
positive-body ((V a ⇒ ⊥) ⇒ h , _) = ⊥ ⇒ ⊥
positive-body ((f ∧ g) ⇒ h , (inr (fisBody , gisBody) , hisHead)) = (positive-body (f ⇒ h , (inr fisBody , hisHead))) ∧ (positive-body (g ⇒ h , (inr gisBody , hisHead)))
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
negative-body : Rule → F
negative-body ((⊥ ⇒ ⊥) ⇒ h , _) = ⊥ ⇒ ⊥
negative-body (V a ⇒ h , _) = ⊥ ⇒ ⊥
negative-body ((V a ⇒ ⊥) ⇒ h , _) = V a ⇒ ⊥
negative-body ((f ∧ g) ⇒ h , (inr (fisBody , gisBody) , hisHead)) = negative-body (f ⇒ h , (inr fisBody , hisHead)) ∧ negative-body (g ⇒ h , (inr gisBody , hisHead))
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
positive-head : Rule → F
positive-head (b ⇒ ⊥ , _) = ⊥
positive-head (b ⇒ V a , _) = V a
positive-head (b ⇒ (V a ⇒ ⊥) , _) = ⊥
positive-head (b ⇒ (f ∨ g) , (bisBody , inr (fisHead , gisHead))) = positive-head (b ⇒ f , (bisBody , inr fisHead)) ∨ positive-head (b ⇒ g , (bisBody , inr gisHead))
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
negative-head : Rule → F
negative-head (b ⇒ ⊥ , _) = ⊥
negative-head (b ⇒ V a , _) = ⊥
negative-head (b ⇒ (V a ⇒ ⊥) , _) = V a ⇒ ⊥
negative-head (b ⇒ (f ∨ g) , (bisBody , inr (fisHead , gisHead))) = negative-head (b ⇒ f , (bisBody , inr fisHead)) ∨ negative-head (b ⇒ g , (bisBody , inr gisHead))
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

rule-reduct : Rule → IPC → F
-- the reduct is defined using two cases
-- 1) if the negative body is not satisfied or the negative head is satisfied we delete the rule
-- 2) otherwise we only keep the positive part of the rule
rule-reduct r i = reduct-r
  where
    -- we start with a helper function that decied which case we use
    decision : F → F → Unit ⊎ Unit
    decision b- h- with dec-C b- i | dec-C h- i
    ... | inr i⊭b- | _        = inl tt
    ... | inl i⊧b- | inr i⊭h- = inr tt
    ... | inl i⊧b- | inl i⊧h- = inl tt

    -- then we build the reduct using the decision and the positive parts of our rule
    build-reduct : (Unit ⊎ Unit) → F → F → F
    build-reduct (inl tt) _  _  = ⊤
    build-reduct (inr tt) b+ h+ = b+ ⇒ h+

    reduct-r = build-reduct (decision (negative-body r) (negative-head r)) (positive-body r) (positive-head r)

lp-reduct : LogicProgram → IPC → Th
lp-reduct ([] , _) i = []
lp-reduct (r ∷ lp , (risRule , lpisLogicProgram)) i = (rule-reduct (r , risRule) i) ∷ (lp-reduct (lp , lpisLogicProgram) i)

_⊧LP-SM_ : IPC → LogicProgram → Set
i ⊧LP-SM lp = (i ⊧C (Th2F (lp-reduct lp i))) × (min-c i (Th2F (lp-reduct lp i)))
