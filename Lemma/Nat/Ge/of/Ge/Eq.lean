import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a x b : ℝ}
-- given
  (h₀ : b ≥ x)
  (h₁ : a = b) :
-- imply
  a ≥ x := by
-- proof
  rw [h₁]
  exact h₀


-- created on 2026-09-27
