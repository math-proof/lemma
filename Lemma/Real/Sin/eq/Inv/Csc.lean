import sympy.functions.elementary.trigonometric
import sympy.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  Real.sin x = 1 / Real.csc x := by
-- proof
  simp [Real.csc]


-- created on 2026-10-17
