module Classical.Tautologies where

open import Classical.Base

-- law of excluded middle ------------------------------------------------------
-- f ∨ ¬f
lem : {f : F} → ValidC (f ∨ (¬ f))
lem {⊥} i = inr (λ x → x)
lem {(V a)} i with i a
... | true  = inl refl
... | false = inr (λ ())
lem {(f ∧ g)} i with lem {f} i
... | inr i⊧C¬f = inr (λ (i⊧Cf , _) → i⊧C¬f i⊧Cf)
... | inl i⊧Cf with lem {g} i
...   | inl i⊧Cg  = inl (i⊧Cf , i⊧Cg)
...   | inr i⊧C¬g = inr (λ (_ , i⊧Cg) → i⊧C¬g i⊧Cg)
lem {(f ∨ g)} i with lem {f} i
... | inl i⊧Cf = inl (inl i⊧Cf)
... | inr i⊧C¬f with lem {g} i
...   | inl i⊧Cg  = inl (inr i⊧Cg)
...   | inr i⊧C¬g = inr [ i⊧C¬f , i⊧C¬g ]
lem {(f ⇒ g)} i with lem {g} i
... | inl i⊧Cg  = inl (λ _ → i⊧Cg)
... | inr i⊧C¬g with lem {f} i
...   | inl i⊧Cf  = inr (λ i⊧Cf⇒g → i⊧C¬g (i⊧Cf⇒g i⊧Cf))
...   | inr i⊧C¬f = inl (λ i⊧Cf → Ø-elim (i⊧C¬f i⊧Cf))

-- ¬¬f is equivalent to f
reduce2¬ : {f : F} → ValidC ((¬ (¬ f)) ⇔ f)
reduce2¬ {f} i = proof⇒ , proof⇐
  where
    proof⇒ : i ⊧C ((¬ (¬ f)) ⇒ f)
    proof⇒ ⊧¬¬f with lem {f} i
    ... | (inl ⊧f)  = ⊧f
    ... | (inr ⊧¬f) = Ø-elim (⊧¬¬f ⊧¬f)

    proof⇐ : i ⊧C (f ⇒ (¬ (¬ f)))
    proof⇐ ⊧f ⊧¬f = ⊧¬f ⊧f
