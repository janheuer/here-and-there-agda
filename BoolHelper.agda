module BoolHelper where

open import Agda.Builtin.Equality using (_β‘_ ; refl)
open import Data.Bool renaming (Bool to πΉ ; _β§_ to _β§πΉ_ ; _β¨_ to _β¨πΉ_ ;
                                not to Β¬πΉ)
                      using (true ; false)
open import Data.Sum.Base using (_β_) renaming (injβ to inl ; injβ to inr)
open import Data.Product using (_Γ_ ; _,_)
open import Relation.Binary.PropositionalEquality.Core using (sym)

-- boolean implication
_βπΉ_ : πΉ β πΉ β πΉ
f βπΉ g = (Β¬πΉ f) β¨πΉ g

contra : {a b : πΉ} β (a β‘ true β b β‘ true) β b β‘ false β a β‘ false
contra {false} {_}     i f = refl
contra {true}  {false} i f = sym (i refl)

-- some helper functions used in the following proofs --------------------------
Γ-to-β§πΉ : {a b : πΉ} β ((a β‘ true) Γ (b β‘ true)) β ((a β§πΉ b) β‘ true)
Γ-to-β§πΉ {true} {true} _ = refl

β§πΉ-to-Γ : {a b : πΉ} β ((a β§πΉ b) β‘ true) β ((a β‘ true) Γ (b β‘ true))
β§πΉ-to-Γ {true} {true} _ = refl , refl

β-to-β¨πΉ : {a b : πΉ} β ((a β‘ true) β (b β‘ true)) β ((a β¨πΉ b) β‘ true)
β-to-β¨πΉ {true}  {_}    (inl _) = refl
β-to-β¨πΉ {false} {true} (inr _) = refl
β-to-β¨πΉ {true}  {true} (inr _) = refl

β¨πΉ-to-β : {a b : πΉ} β ((a β¨πΉ b) β‘ true) β ((a β‘ true) β (b β‘ true))
β¨πΉ-to-β {false} p = inr p
β¨πΉ-to-β {true}  p = inl p

βπΉ-to-β : {a b : πΉ} β ((a βπΉ b) β‘ true) β ((a β‘ false) β (b β‘ true))
βπΉ-to-β {false} {_}    p = inl refl
βπΉ-to-β {true}  {true} p = inr refl

β-to-β§πΉ : {a b : πΉ} β ((a β‘ false) β (b β‘ false)) β ((a β§πΉ b) β‘ false)
β-to-β§πΉ {false} {_}     (inl x) = refl
β-to-β§πΉ {false} {false} (inr y) = refl
β-to-β§πΉ {true}  {false} (inr y) = refl

β§πΉ-to-β : {a b : πΉ} β ((a β§πΉ b) β‘ false) β ((a β‘ false) β (b β‘ false))
β§πΉ-to-β {false} {_}     p = inl refl
β§πΉ-to-β {true}  {false} p = inr refl

Γ-to-β¨πΉ : {a b : πΉ} β ((a β‘ false) Γ (b β‘ false)) β ((a β¨πΉ b) β‘ false)
Γ-to-β¨πΉ {false} {false} p = refl

β¨πΉ-to-Γ : {a b : πΉ} β ((a β¨πΉ b) β‘ false) β ((a β‘ false) Γ (b β‘ false))
β¨πΉ-to-Γ {false} {false} p = refl , refl

Β¬πΉ-f-t : {b : πΉ} β (b β‘ false) β ((Β¬πΉ b) β‘ true)
Β¬πΉ-f-t {false} p = refl

Β¬πΉ-t-f : {b : πΉ} β (b β‘ true) β ((Β¬πΉ b) β‘ false)
Β¬πΉ-t-f {true} p = refl

remove-Β¬πΉ : {a b : πΉ} β ((Β¬πΉ (Β¬πΉ a)) β‘ b) β (a β‘ b)
remove-Β¬πΉ {false} {false} p = refl
remove-Β¬πΉ {true}  {true}  p = refl

β-to-βπΉ : {a b : πΉ} β (a β‘ true β b β‘ true) β a βπΉ b β‘ true
β-to-βπΉ {false} {_} p = refl
β-to-βπΉ {true}  {_} p = p refl

βπΉ-to-β : {a b : πΉ} β (a βπΉ b β‘ true) β a β‘ true β b β‘ true
βπΉ-to-β {false} {false} p = Ξ» x β x
βπΉ-to-β {false} {true}  p = Ξ» x β refl
βπΉ-to-β {true}  {true}  p = Ξ» x β refl
