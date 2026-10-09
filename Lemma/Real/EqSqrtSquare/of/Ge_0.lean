import sympy.core.power
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : x ≥ 0) :
-- imply
  √x² = x :=
-- proof
  Real.sqrt_sq h


-- created on 2025-01-16
