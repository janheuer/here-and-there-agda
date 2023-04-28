module Formula.LogicPrograms.DisjunctiveConjunctive where

open import Agda.Builtin.Unit renaming (⊤ to Unit) using ()
open import Data.Empty renaming (⊥ to Ø) using ()
open import Data.Product using (_×_ ; Σ-syntax)
                         renaming (proj₁ to p1)
open import Data.List using (List ; [] ; _∷_)

open import Formula

-- intermediate form to go from nested rules to rules with double negation
isSC : F → Set
isSC ⊥ = Unit
isSC (⊥ ⇒ ⊥) = Unit
isSC (V a) = Unit
isSC ((V a) ⇒ ⊥) = Unit
isSC (((V a) ⇒ ⊥) ⇒ ⊥) = Unit
isSC (f ∧ g) = (isSC f) × (isSC g)
isSC (f ∨ g) = Ø
isSC (f ⇒ g) = Ø

SC : Set
SC = Σ[ f ∈ F ] (isSC f)

isSD : F → Set
isSD ⊥ = Unit
isSD (⊥ ⇒ ⊥) = Unit
isSD (V a) = Unit
isSD ((V a) ⇒ ⊥) = Unit
isSD (((V a) ⇒ ⊥) ⇒ ⊥) = Unit
isSD (f ∧ g) = Ø
isSD (f ∨ g) = (isSD f) × (isSD g)
isSD (f ⇒ g) = Ø

SD : Set
SD = Σ[ f ∈ F ] (isSD f)

isDNF : F → Set
isDNF (f ∨ g) = (isDNF f) × (isDNF g)
isDNF f = isSC f

DNF : Set
DNF = Σ[ f ∈ F ] (isDNF f)

isCNF : F → Set
isCNF (f ∧ g) = (isCNF f) × (isCNF g)
isCNF f = isSD f

CNF : Set
CNF = Σ[ f ∈ F ] (isCNF f)

isDCR : F → Set
isDCR (f ⇒ g) = (isDNF f) × (isCNF g)
isDCR _ = Ø

DCR : Set
DCR = Σ[ f ∈ F ] (isDCR f)

isDCLP : Th -> Set
isDCLP [] = Unit
isDCLP (r ∷ rs) = (isDCR r) × (isDCLP rs)

DCLP : Set
DCLP = Σ[ t ∈ Th ] (isDCLP t)

DCLP2F : DCLP → F
DCLP2F Π = Th2F (p1 Π)

isDSD : F → Set
isDSD (f ⇒ g) = (isDNF f) × (isSD g)
isDSD _ = Ø

DSD : Set
DSD = Σ[ f ∈ F ] (isDSD f)

isDSDLP : Th → Set
isDSDLP [] = Unit
isDSDLP (r ∷ rs) = (isDSD r) × (isDSDLP rs)

DSDLP : Set
DSDLP = Σ[ t ∈ Th ] (isDSDLP t)

DSDLP2F : DSDLP → F
DSDLP2F Π = Th2F (p1 Π)

isSCD : F → Set
isSCD (f ⇒ g) = (isSC f) × (isSD g)
isSCD _ = Ø

SCD : Set
SCD = Σ[ f ∈ F ] (isSCD f)

isSCDLP : Th → Set
isSCDLP [] = Unit
isSCDLP (r ∷ rs) = (isSCD r) × (isSCDLP rs)

SCDLP : Set
SCDLP = Σ[ t ∈ Th ] (isSCDLP t)

SCDLP2F : SCDLP → F
SCDLP2F Π = Th2F (p1 Π)
