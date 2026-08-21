import sympy.functions.elementary.complexes
import sympy.functions.elementary.trigonometric
import sympy.Basic


@[main]
private lemma main
  {z : ℂ} :
-- imply
  re z = ‖z‖ * Real.cos (arg z) :=
-- proof
  (Complex.norm_mul_cos_arg z).symm


-- created on 2018-06-13
-- updated on 2026-08-20
