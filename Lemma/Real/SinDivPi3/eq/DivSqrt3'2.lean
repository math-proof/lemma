import sympy.functions.elementary.trigonometric
import sympy.Basic


@[main]
private lemma main:
-- imply
  sin (π / 3) = √3 / 2 := by
-- proof
  norm_num [Real.sin_pi_div_three]


-- created on 2025-03-24
