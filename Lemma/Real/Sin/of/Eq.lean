import sympy.functions.elementary.trigonometric
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x = y) :
-- imply
  sin x = sin y := by
-- proof
  rw [h]


-- created on 2018-07-24
