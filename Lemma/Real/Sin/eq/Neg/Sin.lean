import sympy.functions.elementary.trigonometric
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ} :
-- imply
  (x - y).sin = -(y - x).sin := by
-- proof
  rw [Real.sin_sub, Real.sin_sub]
  ring


-- created on 2023-06-02
-- updated on 2023-11-26
