import sympy.core.power
import sympy.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  √x² = |x| := by
-- proof
  rw [Real.sqrt_sq_eq_abs]


-- created on 2025-01-16
