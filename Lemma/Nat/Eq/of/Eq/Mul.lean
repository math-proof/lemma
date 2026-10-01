import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x y c : ℝ}
-- given
  (h₀ : c ≠ 0)
  (h : x * c = y * c) :
-- imply
  x = y := by
-- proof
  exact mul_right_cancel₀ h₀ h


-- created on 2023-11-06
