import sympy.concrete.quantifier
import sympy.Basic


@[path]
private lemma main
  {p q f : α → Prop}
-- given
  (h₀ : ∀ e | p e, f e)
  (h₁ : ∀ e | q e, f e) :
-- imply
  ∀ e | p e ∨ q e, f e := by
-- proof
  intro e he
  obtain hpe | hqe := he
  · exact h₀ e hpe
  · exact h₁ e hqe


-- created on 2026-10-03
