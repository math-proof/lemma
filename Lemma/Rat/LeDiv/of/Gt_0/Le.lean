import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
-- given
  (h₀ : x > 0)
  (h₁ : a ≤ b) :
-- imply
  a / x ≤ b / x := by
-- proof
  exact (div_le_div_iff_of_pos_right h₀).mpr h₁


-- created on 2019-07-31
