import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.LanglandsTunnell.TateLocalZeta
open MeasureTheory LanglandsTunnell.TateLocal Metric
open scoped NNReal ENNReal Pointwise


/-- ported from external source -/

private lemma  distribHaarChar_complex_eq_nnnorm_sq (z : ℂˣ) :
  distribHaarChar ℂ z = ‖(z : ℂ)‖₊ ^ 2 := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := volume) (s := closedBall 0 1)
    (measure_closedBall_pos volume (0:ℂ) one_pos).ne'
    measure_closedBall_lt_top.ne ?_
  rw [Units.smul_def, smul_closedBall' z.ne_zero, smul_zero, mul_one,
    show ‖(z:ℂ)‖ = ‖(z:ℂ)‖ * 1 by ring,
    Measure.addHaar_closedBall_mul volume (0:ℂ) (norm_nonneg _) zero_le_one,
    Complex.finrank_real_complex]
  simp [ENNReal.ofReal_pow (norm_nonneg _), enorm_eq_nnnorm]

private lemma  modulus_complex_eq_nnnorm_sq (z : ℂ) : modulus z = ‖z‖₊ ^ 2 := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  ·
    rw [modulus_of_ne_zero hz, distribHaarChar_complex_eq_nnnorm_sq]
    simp

private lemma  distribHaarChar_real_eq_nnnorm (x : ℝˣ) :
  distribHaarChar ℝ x = ‖(x : ℝ)‖₊ := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := volume) (s := closedBall 0 1)
    (measure_closedBall_pos volume (0:ℝ) one_pos).ne'
    measure_closedBall_lt_top.ne ?_
  rw [Units.smul_def, smul_closedBall' x.ne_zero, smul_zero, mul_one,
    show ‖(x:ℝ)‖ = ‖(x:ℝ)‖ * 1 by ring,
    Measure.addHaar_closedBall_mul volume (0:ℝ) (norm_nonneg _) zero_le_one,
    Module.finrank_self, pow_one]
  simp only [ofReal_norm, enorm_eq_nnnorm]

private lemma  modulus_real_eq_nnnorm (x : ℝ) : modulus x = ‖x‖₊ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  ·
    rw [modulus_of_ne_zero hx, distribHaarChar_real_eq_nnnorm]
    simp
@[path]
private lemma main
  :
-- imply
  ∀ (z : ℂ), modulus z = ‖z‖₊ ^ 2 :=
-- proof
  modulus_complex_eq_nnnorm_sq


-- created on 2026-10-23
