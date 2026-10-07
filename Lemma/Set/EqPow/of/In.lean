import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  (r : ℝ)
  (z : ℂ) :
-- imply
  (Real.exp r : ℂ) ^ z = Complex.exp ((r : ℂ) * z) := by
-- proof
  rw [Complex.cpow_def, if_neg (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero r)),
    ← Complex.ofReal_log (Real.exp_pos r).le, Real.log_exp]


-- created on 2023-04-17
