import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x m M : ℝ}
-- given
  (h₀ : x < M)
  (h₁ : x > m) :
-- imply
  x * x < max (m * m) (M * M) := by
-- proof
  rcases le_total 0 x with hx | hx
  · exact lt_of_lt_of_le (mul_self_lt_mul_self hx h₀) (le_max_right _ _)
  · exact lt_of_lt_of_le (by nlinarith) (le_max_left _ _)


-- created on 2026-09-27
