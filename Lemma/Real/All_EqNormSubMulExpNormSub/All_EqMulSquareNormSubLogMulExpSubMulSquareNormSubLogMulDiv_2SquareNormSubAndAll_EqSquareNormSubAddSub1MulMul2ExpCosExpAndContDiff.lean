import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Complex_norm_one_sub_inv_exp_and_sq_mul_log_eq_and_contDiff](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Complex_norm_one_sub_inv_exp_and_sq_mul_log_eq_and_contDiff.lean)
-/
@[path]
private lemma main :
  -- imply
  (∀ X Θ : ℝ, ‖(1 : ℂ) - (Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ)))⁻¹‖ =
      Real.exp (-(X / 2)) * ‖(1 : ℂ) - Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ))‖) ∧
    (∀ X Θ : ℝ, ‖(1 : ℂ) - (Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ)))⁻¹‖ ^ 2 *
        Real.log ‖(1 : ℂ) - (Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ)))⁻¹‖ =
      Real.exp (-X) *
        (‖(1 : ℂ) - Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ))‖ ^ 2 *
            Real.log ‖(1 : ℂ) - Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ))‖ -
          X / 2 * ‖(1 : ℂ) - Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ))‖ ^ 2)) ∧
    (∀ X Θ : ℝ, ‖(1 : ℂ) - Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ))‖ ^ 2 =
      1 - 2 * Real.exp (X / 2) * Real.cos (2 * Real.pi * Θ) + Real.exp X) ∧
    ContDiff ℝ (⊤ : ENat) (fun p : ℝ × ℝ => 1 - 2 * Real.exp (p.1 / 2) * Real.cos (2 * Real.pi * p.2) + Real.exp p.1) := by
  -- proof
  have hnorm : ∀ X Θ : ℝ, ‖Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ))‖ = Real.exp (X / 2) := by
    intro X Θ
    rw [Complex.norm_exp]
    congr 1
    simp
  have h1 : ∀ X Θ : ℝ, ‖(1 : ℂ) - (Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ)))⁻¹‖ =
    Real.exp (-(X / 2)) * ‖(1 : ℂ) - Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ))‖ := by
    intro X Θ
    set ζ := Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ)) with hζ
    have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
    have : (1 : ℂ) - ζ⁻¹ = ζ⁻¹ * (ζ - 1) := by
      field_simp
    rw [this, norm_mul, norm_inv, hnorm, Real.exp_neg, norm_sub_rev]
  refine ⟨h1, fun X Θ => ?_, fun X Θ => ?_, ?_⟩
  ·
    rw [h1]
    set r := ‖(1 : ℂ) - Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ))‖ with hr
    have hee : Real.exp (-(X / 2)) * Real.exp (-(X / 2)) = Real.exp (-X) := by
      rw [← Real.exp_add]
      ring_nf
    obtain h0 | h0 := eq_or_ne r 0
    ·
      rw [h0]
      simp
    ·
      rw [Real.log_mul (Real.exp_pos _).ne' h0, Real.log_exp, mul_pow, sq, hee]
      ring
  ·
    set a := Real.exp (X / 2) with ha
    have hre : (Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ))).re =
      a * Real.cos (2 * Real.pi * Θ) := by
      rw [Complex.exp_re]
      congr 1
      all_goals simp [ha]
    have him : (Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ))).im =
      a * Real.sin (2 * Real.pi * Θ) := by
      rw [Complex.exp_im]
      congr 1
      all_goals simp [ha]
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, hre, him]
    have hcs := Real.sin_sq_add_cos_sq (2 * Real.pi * Θ)
    have ha2 : a * a = Real.exp X := by
      rw [ha, ← Real.exp_add]
      ring_nf
    linear_combination (a * a) * hcs + ha2
  · apply ((contDiff_const.sub ((contDiff_const.mul (Real.contDiff_exp.comp (contDiff_fst.div_const _))).mul
      (Real.contDiff_cos.comp (contDiff_const.mul contDiff_snd)))).add (Real.contDiff_exp.comp contDiff_fst))


-- created on 2026-10-20
