import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {z : ℂ} :
-- imply
  z.im = ‖z‖ * Real.sin (Complex.arg z) :=
-- proof
  (Complex.norm_mul_sin_arg z).symm


-- created on 2018-07-25
-- updated on 2026-10-26
