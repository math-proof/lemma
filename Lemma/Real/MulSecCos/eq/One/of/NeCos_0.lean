import sympy.functions.elementary.trigonometric
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : Real.cos x ≠ 0) :
-- imply
  Real.sec x * Real.cos x = 1 := by
-- proof
  simp [Real.sec, h]


-- created on 2023-10-03
