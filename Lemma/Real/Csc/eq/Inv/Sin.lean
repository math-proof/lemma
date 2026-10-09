import sympy.functions.elementary.trigonometric
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  -- imply
  : Real.csc x = (Real.sin x)⁻¹ := by
  -- proof
  simp [Real.csc]


-- created on 2026-10-08
