import sympy.core.numbers
import Lemma.Complex.ArgMul.eq.SubAddArgSMul_Ceil.of.Ne_0.Ne_0
open Complex


@[main]
private lemma main
  {A B : ℂ}
-- given
  (hA : A ≠ 0)
  (hB : B ≠ 0)
  (h : ⌈(arg A + arg B) / (2 * π) - 1 / 2⌉ = 1) :
-- imply
  A ^ (3 : ℂ)⁻¹ * B ^ (3 : ℂ)⁻¹ =
    (A * B) ^ (3 : ℂ)⁻¹ * (-(1 / 2) + I * ↑(√3) / 2) := by
-- proof
  have hAB : A * B ≠ 0 := mul_ne_zero hA hB
  rw [cpow_def_of_ne_zero hA, cpow_def_of_ne_zero hB, cpow_def_of_ne_zero hAB]
  have harg : arg (A * B) = arg A + arg B - 2 * π := by
    rw [ArgMul.eq.SubAddArgSMul_Ceil.of.Ne_0.Ne_0 hA hB, h]
    ring
  have hlog : log (A * B) = log A + log B - 2 * π * I := by
    simp only [log, harg, norm_mul]
    rw [Real.log_mul (ne_of_gt (norm_pos_iff.mpr hA)) (ne_of_gt (norm_pos_iff.mpr hB))]
    simp [ofReal_add, ofReal_sub]
    ring
  have hω : exp (2 * π * I / 3) = -(1 / 2) + I * ↑(√3) / 2 := by
    have hmul : (2 * π * I / 3 : ℂ) = ↑(2 * π / 3 : ℝ) * I := by
      simp [div_eq_mul_inv]
      ring
    rw [hmul, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
    have hθ : (2 * π / 3 : ℝ) = π - π / 3 := by ring
    rw [hθ, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
    simp
    ring
  rw [← exp_add]
  have hadd :
      log A * (3 : ℂ)⁻¹ + log B * (3 : ℂ)⁻¹ =
        (log (A * B) + 2 * π * I) * (3 : ℂ)⁻¹ := by
    rw [hlog]
    ring
  rw [hadd, add_mul, exp_add]
  have hdiv : (2 * π * I) * (3 : ℂ)⁻¹ = 2 * π * I / 3 := by field_simp
  rw [hdiv, hω]


@[main]
private lemma zero
  {A B : ℂ}
-- given
  (hA : A ≠ 0)
  (hB : B ≠ 0)
  (h : ⌈(arg A + arg B) / (2 * π) - 1 / 2⌉ = 0) :
-- imply
  A ^ (3 : ℂ)⁻¹ * B ^ (3 : ℂ)⁻¹ = (A * B) ^ (3 : ℂ)⁻¹ := by
-- proof
  have hAB : A * B ≠ 0 := mul_ne_zero hA hB
  rw [cpow_def_of_ne_zero hA, cpow_def_of_ne_zero hB, cpow_def_of_ne_zero hAB]
  have harg : arg (A * B) = arg A + arg B := by
    rw [ArgMul.eq.SubAddArgSMul_Ceil.of.Ne_0.Ne_0 hA hB, h]
    ring
  have hlog : log (A * B) = log A + log B := by
    simp only [log, harg, norm_mul]
    rw [Real.log_mul (ne_of_gt (norm_pos_iff.mpr hA)) (ne_of_gt (norm_pos_iff.mpr hB))]
    simp [ofReal_add]
    ring
  rw [← exp_add]
  have hadd :
      log A * (3 : ℂ)⁻¹ + log B * (3 : ℂ)⁻¹ =
        log (A * B) * (3 : ℂ)⁻¹ := by
    rw [hlog]
    ring
  rw [hadd]


@[main]
private lemma neg
  {A B : ℂ}
-- given
  (hA : A ≠ 0)
  (hB : B ≠ 0)
  (h : ⌈(arg A + arg B) / (2 * π) - 1 / 2⌉ = -1) :
-- imply
  A ^ (3 : ℂ)⁻¹ * B ^ (3 : ℂ)⁻¹ =
    (A * B) ^ (3 : ℂ)⁻¹ * (-(1 / 2) - I * ↑(√3) / 2) := by
-- proof
  have hAB : A * B ≠ 0 := mul_ne_zero hA hB
  rw [cpow_def_of_ne_zero hA, cpow_def_of_ne_zero hB, cpow_def_of_ne_zero hAB]
  have harg : arg (A * B) = arg A + arg B + 2 * π := by
    rw [ArgMul.eq.SubAddArgSMul_Ceil.of.Ne_0.Ne_0 hA hB, h]
    ring
  have hlog : log (A * B) = log A + log B + 2 * π * I := by
    simp only [log, harg, norm_mul]
    rw [Real.log_mul (ne_of_gt (norm_pos_iff.mpr hA)) (ne_of_gt (norm_pos_iff.mpr hB))]
    simp [ofReal_add]
    ring
  have hω : exp (-2 * π * I / 3) = -(1 / 2) - I * ↑(√3) / 2 := by
    have hmul : (-2 * π * I / 3 : ℂ) = ↑(-2 * π / 3 : ℝ) * I := by
      simp [div_eq_mul_inv]
      ring
    rw [hmul, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
    have hθ : (-2 * π / 3 : ℝ) = -(π - π / 3) := by ring
    rw [hθ, Real.cos_neg, Real.sin_neg, Real.cos_pi_sub, Real.sin_pi_sub,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
    simp
    ring
  rw [← exp_add]
  have hadd :
      log A * (3 : ℂ)⁻¹ + log B * (3 : ℂ)⁻¹ =
        (log (A * B) + -2 * π * I) * (3 : ℂ)⁻¹ := by
    rw [hlog]
    ring
  rw [hadd, add_mul, exp_add]
  have hdiv : (-2 * π * I) * (3 : ℂ)⁻¹ = -2 * π * I / 3 := by field_simp
  rw [hdiv, hω]


-- created on 2018-10-26
-- updated on 2026-08-20
