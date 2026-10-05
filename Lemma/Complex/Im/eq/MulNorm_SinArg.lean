import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import sympy.Basic


@[main]
private lemma main
  {z : ℂ} :
-- imply
  z.im = ‖z‖ * Real.sin (Complex.arg z) :=
-- proof
  (Complex.norm_mul_sin_arg z).symm


-- created on 2018-07-25
-- updated on 2022-01-23
