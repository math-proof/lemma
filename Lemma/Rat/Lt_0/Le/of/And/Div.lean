import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x a b : ℝ}
-- given
  (h₀ : x < 0)
  (h₁ : a / x ≥ b / x) :
-- imply
  x < 0 ∧ a ≤ b := by
-- proof
  exact ⟨h₀, (div_le_div_right_of_neg h₀).mp h₁⟩


-- created on 2026-09-27
