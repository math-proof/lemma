import sympy.functions.elementary.complexes
import sympy.Basic


/-- `ω = -1/2 + i√3/2 = exp(2πi/3)`. -/
@[path]
private lemma main :
-- imply
  (-1 / 2 + Complex.I * √3 / 2 : ℂ) = Complex.exp (↑(2 * π / 3) * Complex.I) := by
-- proof
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have e : 2 * π / 3 = π - π / 3 := by ring
  rw [e, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast
  ring


-- created on 2026-10-07
