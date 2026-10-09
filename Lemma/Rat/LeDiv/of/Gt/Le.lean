import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y a b : ℝ}
-- given
  (h₀ : x > y)
  (h₁ : a ≤ b) :
-- imply
  a / (x - y) ≤ b / (x - y) := by
-- proof
  exact (div_le_div_iff_of_pos_right (sub_pos.mpr h₀)).mpr h₁


-- created on 2019-08-01
