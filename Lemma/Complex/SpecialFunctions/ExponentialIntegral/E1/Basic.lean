import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.SpecialFunctions.ExponentialIntegral.E1.Basic
open Complex


namespace Complex

/--
[two_term_kernel_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/Basic.lean)
-/
@[path]
lemma two_term_kernel_identity
  {z : ℂ}
  {t : ℝ}
-- given
  (hz : z ≠ 0)
  (htz : (t : ℂ) + z ≠ 0) :
-- imply
  1 / ((t : ℂ) + z) = 1 / z - (t : ℂ) / z ^ 2 + (t : ℂ) ^ 2 / (z ^ 2 * ((t : ℂ) + z)) := by
-- proof
  field_simp
  ring

end Complex

namespace Complex

/--
[integrableOn_exp_neg_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/Basic.lean)
-/
@[path]
lemma integrableOn_exp_neg_mul_pow
  {n : ℕ} :
-- imply
  MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ n) (Set.Ioi 0) := by
-- proof
  simpa using
    (Real.GammaIntegral_convergent (s := (n : ℝ) + 1) (by positivity))

end Complex

namespace Complex

/--
[integral_exp_neg_mul_pow_Ioi](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/Basic.lean)
-/
@[path]
lemma integral_exp_neg_mul_pow_Ioi
  {n : ℕ} :
-- imply
  ∫ t : ℝ in Set.Ioi 0, Real.exp (-t) * t ^ n = (n.factorial : ℝ) := by
-- proof
  calc
    ∫ t : ℝ in Set.Ioi 0, Real.exp (-t) * t ^ n = Real.Gamma ((n : ℝ) + 1) := by
      simpa using
        (Real.Gamma_eq_integral (s := (n : ℝ) + 1) (by positivity)).symm
    _ = (n.factorial : ℝ) := Real.Gamma_nat_eq_factorial n

end Complex

namespace Complex

/--
[outer_sector_sin_abs_arg_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/Basic.lean)
-/
@[path]
lemma outer_sector_sin_abs_arg_pos
  {z : ℂ}
-- given
  (_hz : z ≠ 0)
  (hargLower : Real.pi / 2 ≤ |z.arg|)
  (hargUpper : |z.arg| < Real.pi) :
-- imply
  0 < Real.sin |z.arg| := by
-- proof
  exact Real.sin_pos_of_pos_of_lt_pi
    (Real.pi_div_two_pos.trans_le hargLower) hargUpper

end Complex

namespace Complex

/--
[outer_sector_distance](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/Basic.lean)
-/
@[path]
lemma outer_sector_distance
  {z : ℂ}
  {t : ℝ}
-- given
  (_hz : z ≠ 0)
  (_ht : 0 ≤ t)
  (_hargLower : Real.pi / 2 ≤ |z.arg|)
  (_hargUpper : |z.arg| < Real.pi) :
-- imply
  ‖z‖ * Real.sin |z.arg| ≤ ‖(t : ℂ) + z‖ := by
-- proof
  calc
    ‖z‖ * Real.sin |z.arg| = |‖z‖ * Real.sin z.arg| := by
      rw [abs_mul, abs_norm,
        Real.abs_sin_eq_sin_abs_of_abs_le_pi (Complex.abs_arg_le_pi z)]
    _ = |z.im| := by rw [Complex.norm_mul_sin_arg]
    _ = |((t : ℂ) + z).im| := by simp
    _ ≤ ‖(t : ℂ) + z‖ := Complex.abs_im_le_norm _

end Complex

namespace Complex

/--
[integral_remainder_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/Basic.lean)
-/
@[path]
lemma integral_remainder_bound
  {z : ℂ}
-- given
  (hz : z ≠ 0)
  (hargLower : Real.pi / 2 ≤ |z.arg|)
  (hargUpper : |z.arg| < Real.pi) :
-- imply
  ‖Complex.exp (-z) / z^2 *
    ∫ t : ℝ in Set.Ioi 0,
    (Real.exp (-t) : ℂ) * (t : ℂ)^2 / ((t : ℂ) + z)‖
    ≤ (Real.sin |z.arg|)⁻¹ * ‖e1AsymptoticTerm 2 z hz‖ := by
-- proof
  have hs : 0 < Real.sin |z.arg| :=
    outer_sector_sin_abs_arg_pos z hz hargLower hargUpper
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hd : 0 < ‖z‖ * Real.sin |z.arg| := mul_pos hzn hs
  have hg : MeasureTheory.IntegrableOn
    (fun t : ℝ => (‖z‖ * Real.sin |z.arg|)⁻¹ * (Real.exp (-t) * t ^ 2))
    (Set.Ioi 0) :=
    (integrableOn_exp_neg_mul_pow 2).const_mul _
  have hInt :
    ∫ t : ℝ in Set.Ioi 0,
      ‖(Real.exp (-t) : ℂ) * (t : ℂ)^2 / ((t : ℂ) + z)‖
      ≤ ∫ t : ℝ in Set.Ioi 0,
        (‖z‖ * Real.sin |z.arg|)⁻¹ * (Real.exp (-t) * t ^ 2) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hg ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    have hdist : ‖z‖ * Real.sin |z.arg| ≤ ‖(t : ℂ) + z‖ :=
      outer_sector_distance z t hz ht0 hargLower hargUpper
    calc
      ‖(Real.exp (-t) : ℂ) * (t : ℂ)^2 / ((t : ℂ) + z)‖ =
        (Real.exp (-t) * t ^ 2) / ‖(t : ℂ) + z‖ := by
          simp [norm_pow, Complex.norm_real,
            Real.norm_eq_abs, Complex.norm_exp,
            abs_of_nonneg ht0]
      _ ≤ (Real.exp (-t) * t ^ 2) / (‖z‖ * Real.sin |z.arg|) := by
        exact div_le_div_of_nonneg_left (mul_nonneg (Real.exp_pos _).le (sq_nonneg t))
          hd hdist
      _ = (‖z‖ * Real.sin |z.arg|)⁻¹ * (Real.exp (-t) * t ^ 2) := by
        rw [div_eq_inv_mul]
  calc
    ‖Complex.exp (-z) / z^2 *
      ∫ t : ℝ in Set.Ioi 0,
        (Real.exp (-t) : ℂ) * (t : ℂ)^2 / ((t : ℂ) + z)‖ =
      ‖Complex.exp (-z) / z^2‖ *
        ‖∫ t : ℝ in Set.Ioi 0,
          (Real.exp (-t) : ℂ) * (t : ℂ)^2 / ((t : ℂ) + z)‖ := by
      rw [norm_mul]
    _ ≤ ‖Complex.exp (-z) / z^2‖ *
      (∫ t : ℝ in Set.Ioi 0,
        ‖(Real.exp (-t) : ℂ) * (t : ℂ)^2 / ((t : ℂ) + z)‖) := by
      exact mul_le_mul_of_nonneg_left
        (MeasureTheory.norm_integral_le_integral_norm
          (μ := MeasureTheory.volume.restrict (Set.Ioi 0))
          (fun t : ℝ =>
            (Real.exp (-t) : ℂ) * (t : ℂ)^2 / ((t : ℂ) + z)))
        (norm_nonneg _)
    _ ≤ ‖Complex.exp (-z) / z^2‖ *
      (∫ t : ℝ in Set.Ioi 0,
        (‖z‖ * Real.sin |z.arg|)⁻¹ * (Real.exp (-t) * t ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hInt (norm_nonneg _)
    _ = (Real.sin |z.arg|)⁻¹ * ‖e1AsymptoticTerm 2 z hz‖ := by
      rw [MeasureTheory.integral_const_mul, integral_exp_neg_mul_pow_Ioi]
      simp [e1AsymptoticTerm, e1AsymptoticTermRaw, norm_pow, Complex.norm_exp,
        Nat.factorial]
      field_simp
end



-- created on 2026-10-20
-- updated on 2026-10-23
