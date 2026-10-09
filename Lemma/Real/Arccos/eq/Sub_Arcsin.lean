import sympy.Basic
import sympy.functions.elementary.trigonometric


@[path]
private lemma main
  {x : ℝ} :
-- imply
  arccos x = π / 2 - arcsin x :=
-- proof
  Real.arccos_eq_pi_div_two_sub_arcsin x


-- created on 2018-06-13
