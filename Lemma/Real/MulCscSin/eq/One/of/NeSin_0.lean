import sympy.functions.elementary.trigonometric
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : Real.sin x ≠ 0) :
-- imply
  Real.csc x * Real.sin x = 1 := by
-- proof
  simp [Real.csc, h]


-- created on 2026-10-17
