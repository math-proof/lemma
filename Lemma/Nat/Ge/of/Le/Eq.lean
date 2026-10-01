import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b x : ℝ}
-- given
  (h₀ : a ≤ x)
  (h₁ : b = x) :
-- imply
  b ≥ a := by
-- proof
  rw [h₁]
  exact h₀


-- created on 2026-09-27
