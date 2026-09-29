import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b x : ℝ}
-- given
  (h₀ : a ≤ x)
  (h₁ : x ≤ b) :
-- imply
  b ≥ a := by
-- proof
  exact le_trans h₀ h₁


-- created on 2026-09-27
