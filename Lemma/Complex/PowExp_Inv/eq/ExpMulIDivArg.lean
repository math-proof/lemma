import sympy.core.numbers
import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
-- given
  (x : ℝ)
  (m : ℕ) :
-- imply
  (I * x).exp ^ (m : ℂ)⁻¹ = (I * (arg ((I * x).exp) / (m : ℂ))).exp := by
-- proof
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _)]
  rw [Complex.log, mul_comm I (x : ℂ), Complex.norm_exp_ofReal_mul_I, Real.log_one, Complex.ofReal_zero, zero_add]
  congr 1
  ring


-- created on 2018-08-21
-- updated on 2026-08-20
