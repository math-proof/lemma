import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y a b : ℝ}
-- given
  (h₀ : x < y)
  (h₁ : a ≤ b) :
-- imply
  a / (y - x) ≤ b / (y - x) := by
-- proof
  exact (div_le_div_iff_of_pos_right (sub_pos.mpr h₀)).mpr h₁


-- created on 2026-09-27
