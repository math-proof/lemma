import sympy.functions.elementary.trigonometric
import Lemma.Complex.ExpMulI.eq.AddCos_MulISin


/--
| attributes | lemma |
| :---: | :---: |
| main | Complex.ExpMulIDivMul2Pi3.eq.Add_MulI |
| comm | Complex.Add_MulI.eq.ExpMulIDivMul2Pi3 |
-/
@[main, comm]
private lemma main :
-- imply
  (I * (2 * π / 3)).exp = ↑(-(1 / 2 : ℝ)) + I * ↑(√3 / 2 : ℝ) := by
-- proof
  rw [Complex.ExpMulI.eq.AddCos_MulISin]
  have : (2 * π / 3 : ℂ) = ↑(2 * π / 3 : ℝ) := by
    simp [div_eq_mul_inv]
  rw [this, ← Complex.ofReal_cos, ← Complex.ofReal_sin, (by ring : (2 * π / 3 : ℝ) = π - π / 3), Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]


-- created on 2026-08-29
