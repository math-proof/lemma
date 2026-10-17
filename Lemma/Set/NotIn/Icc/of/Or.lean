import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {e a b : ℝ}
-- given
  (h₀ : e < a ∨ e ≥ b) :
-- imply
  e ∉ Set.Ico a b := by
-- proof
  intro h₁
  obtain hlt | hge := h₀
  · linarith [h₁.1]
  · linarith [h₁.2]


-- created on 2026-10-11
-- updated on 2026-10-17
