import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given.scale.positive
  {x y z : ℝ}
-- given
  (h₀ : x / z < y / z)
  (h₁ : z > 0) :
-- imply
  x < y := by
-- proof
  exact (div_lt_div_iff_of_pos_right h₁).mp h₀


-- created on 2026-09-27
