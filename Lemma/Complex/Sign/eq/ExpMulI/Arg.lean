import sympy.functions.elementary.complexes
import sympy.Basic
open Real


@[main]
private lemma main
  {z : ℂ}
-- given
  (h : z ≠ 0) :
-- imply
  Complex.sign z = Complex.exp (Complex.I * arg z) := by
-- proof
  unfold Complex.sign
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
  rw [div_eq_iff hn, mul_comm Complex.I, mul_comm]
  exact (Complex.norm_mul_exp_arg_mul_I z).symm


-- created on 2026-09-27
