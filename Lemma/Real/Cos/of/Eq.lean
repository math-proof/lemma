import sympy.functions.elementary.trigonometric
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x = y) :
-- imply
  cos x = cos y := by
-- proof
  rw [h]


-- created on 2026-08-18
