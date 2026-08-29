import sympy.functions.elementary.complexes
import sympy.functions.elementary.trigonometric
import Lemma.Complex.ExpMulI.eq.AddCos_MulISin


/--
| attributes | lemma |
| :---: | :---: |
| main | Complex.ExpMulIDivMulNeg2Pi3.eq.Sub_MulI |
| comm | Complex.Sub_MulI.eq.ExpMulIDivMulNeg2Pi3 |
-/
@[main, comm]
private lemma main :
-- imply
  (I * (-2 * π / 3)).exp = ↑(-(1 / 2 : ℝ)) - I * ↑(√3 / 2 : ℝ) := by
-- proof
  rw [Complex.ExpMulI.eq.AddCos_MulISin]
  have : (-2 * π / 3 : ℂ) = ↑(-2 * π / 3 : ℝ) := by
    simp [div_eq_mul_inv]
  rw [this, ← Complex.ofReal_cos, ← Complex.ofReal_sin, (by ring : (-2 * π / 3 : ℝ) = -(π - π / 3)), Real.cos_neg, Real.sin_neg, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  simp [Complex.ofReal_neg, sub_eq_add_neg]


-- created on 2026-08-29
