import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {z : ℂ} :
-- imply
  z.re = ‖z‖ * Real.cos (Complex.arg z) :=
-- proof
  (Complex.norm_mul_cos_arg z).symm


-- created on 2018-06-13
-- updated on 2026-10-26
