import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {z : ℂ}
-- given
  (h₀ : z ≠ 0) :
-- imply
  z / ‖z‖ = Complex.cos (Complex.arg z) + Complex.sin (Complex.arg z) * Complex.I := by
-- proof
  have h := (Complex.norm_mul_cos_add_sin_mul_I z).symm
  have h₂ : (‖z‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr h₀
  rwa [div_eq_iff h₂, mul_comm]


-- created on 2023-05-25
-- updated on 2026-10-26
