import sympy.concrete.quantifier
import sympy.Basic


@[main, mp, mpr]
private lemma main
-- given
  (f p : α → Prop) :
-- imply
  (∀ e, f e) ↔ (∀ e | p e, f e) ∧ (∀ e | ¬p e, f e) := by
-- proof
  constructor
  .
    aesop
  .
    rintro ⟨h₁, h₂⟩ e
    by_cases hp : p e <;>
      aesop


-- created on 2025-08-04
