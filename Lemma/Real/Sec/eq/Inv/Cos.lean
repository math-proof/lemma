import sympy.functions.elementary.trigonometric
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
  -- imply
  : Real.sec x = (Real.cos x)⁻¹ := by
  -- proof
  simp [Real.sec]


-- created on 2026-10-08
