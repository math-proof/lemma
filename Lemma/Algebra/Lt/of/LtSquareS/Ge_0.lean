import sympy.core.power
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
-- given
  (h₀ : a² < b²)
  (h₁ : b ≥ 0) :
-- imply
  a < b := by
-- proof
  -- Apply the square root to both sides of the inequality a^2 < b^2
  apply lt_of_pow_lt_pow_left₀ 2 (by linarith) (by linarith)


-- created on 2025-04-06
