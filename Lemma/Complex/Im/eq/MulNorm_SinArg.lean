import sympy.functions.elementary.complexes
import sympy.functions.elementary.trigonometric
import sympy.Basic


@[main]
private lemma main
  {z : ℂ} :
-- imply
  im z = ‖z‖ * Real.sin (arg z) :=
-- proof
  (Complex.norm_mul_sin_arg z).symm


-- created on 2018-07-25
-- updated on 2026-08-20
