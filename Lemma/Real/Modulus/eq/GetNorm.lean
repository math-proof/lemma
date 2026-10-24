import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_LanglandsTunnell_TateLocalZeta
open MeasureTheory LanglandsTunnell.TateLocal Metric
open scoped NNReal ENNReal Pointwise


private lemma  distribHaarChar_complex_eq_nnnorm_sq (z : ℂˣ) :
  distribHaarChar ℂ z = nnnorm (z : ℂ) ^ 2 := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := volume) (s := closedBall 0 1)
    (measure_closedBall_pos volume (0:ℂ) one_pos).ne'
    measure_closedBall_lt_top.ne ?_
  rw [Units.smul_def, smul_closedBall' z.ne_zero, smul_zero, mul_one,
    show ‖(z:ℂ)‖ = ‖(z:ℂ)‖ * 1 by ring,
    Measure.addHaar_closedBall_mul volume (0:ℂ) (norm_nonneg _) zero_le_one,
    Complex.finrank_real_complex]
  simp [ENNReal.ofReal_pow (norm_nonneg _), enorm_eq_nnnorm]

private lemma  modulus_complex_eq_nnnorm_sq (z : ℂ) : modulus z = nnnorm z ^ 2 := by
  if hz : z = 0 then
    simp [hz]
  else
    rw [modulus_of_ne_zero hz, distribHaarChar_complex_eq_nnnorm_sq]
    simp

private lemma  distribHaarChar_real_eq_nnnorm (x : ℝˣ) :
  distribHaarChar ℝ x = nnnorm (x : ℝ) := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := volume) (s := closedBall 0 1)
    (measure_closedBall_pos volume (0:ℝ) one_pos).ne'
    measure_closedBall_lt_top.ne ?_
  rw [Units.smul_def, smul_closedBall' x.ne_zero, smul_zero, mul_one,
    show ‖(x:ℝ)‖ = ‖(x:ℝ)‖ * 1 by ring,
    Measure.addHaar_closedBall_mul volume (0:ℝ) (norm_nonneg _) zero_le_one,
    Module.finrank_self, pow_one]
  simp only [ofReal_norm, enorm_eq_nnnorm]

private lemma  modulus_real_eq_nnnorm (x : ℝ) : modulus x = nnnorm x := by
  if hx : x = 0 then
    simp [hx]
  else
    rw [modulus_of_ne_zero hx, distribHaarChar_real_eq_nnnorm]
    simp
/--
[LanglandsTunnell_TateLocal_modulus_real_eq_nnnorm](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LanglandsTunnell_TateLocal_modulus_real_eq_nnnorm.lean)
-/
@[path]
private lemma main
  :
-- imply
  ∀ (x : ℝ), modulus x = nnnorm x :=
-- proof
  modulus_real_eq_nnnorm


-- created on 2026-10-23
