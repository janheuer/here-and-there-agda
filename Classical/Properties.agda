module Classical.Properties where

open import Agda.Builtin.Equality using (refl ; _≡_)
open import Data.Bool renaming (Bool to 𝔹) using (true ; false)
open import Data.Empty renaming (⊥-elim to Ø-elim ; ⊥ to Ø) using ()
open import Data.Product using (_,_)
open import Data.Sum renaming (inj₁ to inl ; inj₂ to inr) using (_⊎_ ; [_,_])

open import Classical.Base

-- if ¬f and f hold every formula holds ----------------------------------------
contraC : {i : IPC} → {f : F} → i ⊧C (¬ f) → i ⊧C f → (g : F) → i ⊧C g
-- note that i ⊧C (¬ f) is (i ⊧C f) → Ø by definition
contraC {i} {f} ⊭Cf ⊧Cf g = Ø-elim (⊭Cf ⊧Cf)

-- ⊤ holds in every interpretation ---------------------------------------------
validC-⊤ : ValidC ⊤
validC-⊤ i = λ ()

-- law of excluded middle ------------------------------------------------------
-- for every formula f the formula f ∨ ¬f is valid
law-of-excluded-middle : (f : F) → ValidC (f ∨ (¬ f))
law-of-excluded-middle (⊥) i = inr (validC-⊤ i)
law-of-excluded-middle (V a) i with i a
-- i ⊧C a is i a ≡ true
... | true  = inl refl
-- i ⊧C (¬ a) is (i ⊧C a) → Ø which in turn is (i a ≡ true) → Ø
... | false = inr (λ ())
law-of-excluded-middle (f ∧ g) i with law-of-excluded-middle f i
-- if ¬f holds then ¬(f ∧ g) also holds
... | inr i⊧C¬f = inr (λ (i⊧Cf , _) → i⊧C¬f i⊧Cf)
-- otherwise we need to check whether g holds
... | inl i⊧Cf with law-of-excluded-middle g i
-- both f and g hold
...   | inl i⊧Cg  = inl (i⊧Cf , i⊧Cg)
-- as ¬g holds also ¬(f ∧ g) holds
...   | inr i⊧C¬g = inr (λ (_ , i⊧Cg) → i⊧C¬g i⊧Cg)
law-of-excluded-middle (f ∨ g) i with law-of-excluded-middle f i
-- if f holds (f ∨ g) holds
... | inl i⊧Cf = inl (inl i⊧Cf)
-- otherwise we check g
... | inr i⊧C¬f with law-of-excluded-middle g i
-- if g holds (f ∨ g) holds
...   | inl i⊧Cg  = inl (inr i⊧Cg)
-- otherwise both ¬f and ¬g hold and thus ¬(f ∨ g) holds
...   | inr i⊧C¬g = inr [ i⊧C¬f , i⊧C¬g ]
law-of-excluded-middle (f ⇒ g) i with law-of-excluded-middle g i
-- if g holds we can show f⇒g by just ignoring the proof of f
... | inl i⊧Cg  = inl (λ _ → i⊧Cg)
-- otherwise we check whether f holds
... | inr i⊧C¬g with law-of-excluded-middle f i
-- if f holds we can proof that ¬(f⇒g) holds
-- i.e. we can derive a contradiction assuming that f⇒g holds
-- as we have ¬g, and get g by applying the proof of f⇒g to the proof of f
...   | inl i⊧Cf  = inr (λ i⊧Cf⇒g → i⊧C¬g (i⊧Cf⇒g i⊧Cf))
-- if ¬f holds we can show that f⇒g holds
-- as we have a contradicition if f also holds
...   | inr i⊧C¬f = inl (λ i⊧Cf → contraC i⊧C¬f i⊧Cf g)

-- decidability of classical logic
dec-C : (f : F) → (i : IPC) → (i ⊧C f) ⊎ ((i ⊧C f) → Ø)
dec-C f i = law-of-excluded-middle f i

-- ¬¬f is equivalent to f
reduce2¬ : {f : F} → ValidC ((¬ (¬ f)) ⇔ f)
reduce2¬ {f} i = proof⇒ , proof⇐
  where
    proof⇒ : i ⊧C ((¬ (¬ f)) ⇒ f)
    -- we use the law of excluded middle for f
    proof⇒ ⊧¬¬f with law-of-excluded-middle f i
    -- if f holds we are done
    ... | (inl ⊧f)  = ⊧f
    -- otherwise we have a contradiction as both ¬f and ¬(¬f) hold
    ... | (inr ⊧¬f) = contraC {f = (¬ f)} ⊧¬¬f ⊧¬f f

    proof⇐ : i ⊧C (f ⇒ (¬ (¬ f)))
    -- given f we proof ¬¬f
    -- that is given (f and) ¬f we derive a contradiction
    proof⇐ ⊧f ⊧¬f = ⊧¬f ⊧f
