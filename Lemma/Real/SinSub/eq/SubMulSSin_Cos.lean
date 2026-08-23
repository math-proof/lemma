import sympy.functions.elementary.trigonometric
import sympy.Basic


@[main, comm]
private lemma main
-- given
  (x y : ℝ) :
-- imply
  (x - y).sin = x.sin * y.cos - y.sin * x.cos := by
-- proof
  grind [Real.sin_sub]


-- created on 2020-11-24
-- updated on 2026-08-23
