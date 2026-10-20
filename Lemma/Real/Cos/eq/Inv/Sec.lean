import sympy.functions.elementary.trigonometric
import sympy.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  Real.cos x = 1 / Real.sec x := by
-- proof
  simp [Real.sec]


-- created on 2023-11-26
