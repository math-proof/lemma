import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.SpecialFunctions.ExponentialIntegral.E1.TwoTermRemainder
open Filter Set Topology MeasureTheory
open Complex


namespace Complex

/--
[slitPlane_of_arg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/TwoTermRemainder.lean)
-/
@[path]
private lemma slitPlane_of_arg {z : ℂ} (hz : z ≠ 0) (harg : |z.arg| < Real.pi) :
  z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff_arg]
  refine ⟨?_, hz⟩
  intro h
  rwa [h, abs_of_nonneg Real.pi_nonneg] at harg

end Complex

namespace Complex

/--
[exists_pos_le_norm_add_of_slitPlane](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/TwoTermRemainder.lean)
-/
@[path]
private lemma exists_pos_le_norm_add_of_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) :
  ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, 0 ≤ t → d ≤ ‖(t : ℂ) + z‖ := by
  rw [Complex.mem_slitPlane_iff] at hz
  obtain hzre | hzim := hz
  · refine ⟨z.re, hzre, ?_⟩
    intro t ht
    calc
      z.re ≤ t + z.re := by linarith
      _ = ((t : ℂ) + z).re := by simp
      _ ≤ ‖(t : ℂ) + z‖ := Complex.re_le_norm _
  · refine ⟨|z.im|, abs_pos.mpr hzim, ?_⟩
    intro t _
    calc
      |z.im| = |((t : ℂ) + z).im| := by simp
      _ ≤ ‖(t : ℂ) + z‖ := Complex.abs_im_le_norm _

end Complex

namespace Complex

/--
[integrableOn_exp_neg_mul_pow_div_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/TwoTermRemainder.lean)
-/
@[path]
private lemma integrableOn_exp_neg_mul_pow_div_add (n : ℕ) {z : ℂ}
  (hz : z ∈ Complex.slitPlane) :
  IntegrableOn
    (fun t : ℝ => (Real.exp (-t) : ℂ) * (t : ℂ) ^ n / ((t : ℂ) + z))
    (Ioi 0) := by
  obtain ⟨d, hd, hdist⟩ := exists_pos_le_norm_add_of_slitPlane hz
  have hg : IntegrableOn
    (fun t : ℝ => d⁻¹ * (Real.exp (-t) * t ^ n)) (Ioi 0) :=
    (integrableOn_exp_neg_mul_pow n).const_mul d⁻¹
  refine hg.mono' ?_ ?_
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply ContinuousOn.div
    · exact (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp continuous_neg)).continuousOn.mul
        ((Complex.continuous_ofReal.comp continuous_id).pow n).continuousOn
    · exact (Complex.continuous_ofReal.comp continuous_id).continuousOn.add continuousOn_const
    · intro t ht
      exact norm_pos_iff.mp (hd.trans_le (hdist t ht.le))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := ht.le
    calc
      ‖(Real.exp (-t) : ℂ) * (t : ℂ) ^ n / ((t : ℂ) + z)‖ =
        (Real.exp (-t) * t ^ n) / ‖(t : ℂ) + z‖ := by
        rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real]
        simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_nonneg ht0]
      _ ≤ (Real.exp (-t) * t ^ n) / d := by
        exact div_le_div_of_nonneg_left
          (mul_nonneg (Real.exp_pos _).le (pow_nonneg ht0 n)) hd (hdist t ht0)
      _ = d⁻¹ * (Real.exp (-t) * t ^ n) := by rw [div_eq_inv_mul]

end Complex

namespace Complex

/--
[integral_complex_exp_moment](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/TwoTermRemainder.lean)
-/
@[path]
private lemma integral_complex_exp_moment (n : ℕ) :
  ∫ t : ℝ in Ioi 0, (Real.exp (-t) : ℂ) * (t : ℂ) ^ n = (n.factorial : ℂ) := by
  calc
    ∫ t : ℝ in Ioi 0, (Real.exp (-t) : ℂ) * (t : ℂ) ^ n =
      ∫ t : ℝ in Ioi 0, ((Real.exp (-t) * t ^ n : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with t
      push_cast
      ring
    _ = ((∫ t : ℝ in Ioi 0, Real.exp (-t) * t ^ n : ℝ) : ℂ) := by
      simpa using (integral_complex_ofReal
        (f := fun t : ℝ => Real.exp (-t) * t ^ n)
        (μ := volume.restrict (Ioi 0)))
    _ = (n.factorial : ℂ) := by
      rw [integral_exp_neg_mul_pow_Ioi]
      norm_cast

end Complex

namespace Complex

/--
[two_term_integral_remainder](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/TwoTermRemainder.lean)
-/
@[path]
lemma two_term_integral_remainder
  {z : ℂ}
-- given
  (hz : z ≠ 0)
  (harg : |z.arg| < Real.pi) :
-- imply
  e1AsymptoticRemainder 2 z hz =
    Complex.exp (-z) / z^2 *
    ∫ t : ℝ in Ioi 0,
    (Real.exp (-t) : ℂ) * (t : ℂ)^2 / ((t : ℂ) + z) := by
-- proof
  have hzslit := slitPlane_of_arg hz harg
  let K : ℝ → ℂ := fun t =>
    (Real.exp (-t) : ℂ) / ((t : ℂ) + z)
  let M0 : ℝ → ℂ := fun t => (Real.exp (-t) : ℂ)
  let M1 : ℝ → ℂ := fun t => (Real.exp (-t) : ℂ) * (t : ℂ)
  let R : ℝ → ℂ := fun t =>
    (Real.exp (-t) : ℂ) * (t : ℂ)^2 / ((t : ℂ) + z)
  have hM0 : IntegrableOn M0 (Ioi 0) := by
    change Integrable (fun t : ℝ => (Real.exp (-t) : ℂ)) (volume.restrict (Ioi 0))
    apply Integrable.congr (integrableOn_exp_neg_mul_pow 0).ofReal
    filter_upwards with t
    simp only [RCLike.ofReal_eq_complex_ofReal, pow_zero, mul_one]
  have hM1 : IntegrableOn M1 (Ioi 0) := by
    change Integrable
      (fun t : ℝ => (Real.exp (-t) : ℂ) * (t : ℂ)) (volume.restrict (Ioi 0))
    apply Integrable.congr (integrableOn_exp_neg_mul_pow 1).ofReal
    filter_upwards with t
    simp only [RCLike.ofReal_eq_complex_ofReal, RCLike.ofReal_mul, pow_one]
  have hR : IntegrableOn R (Ioi 0) := by
    simpa only [R] using integrableOn_exp_neg_mul_pow_div_add 2 hzslit
  have hK_ae : K =ᵐ[volume.restrict (Ioi 0)]
    fun t => (1 / z) * M0 t - (1 / z^2) * M1 t + (1 / z^2) * R t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htz : (t : ℂ) + z ≠ 0 := by
      obtain ⟨d, hd, hdist⟩ := exists_pos_le_norm_add_of_slitPlane hzslit
      exact norm_ne_zero_iff.mp (ne_of_gt (hd.trans_le (hdist t ht.le)))
    have hkernel := two_term_kernel_identity z t hz htz
    dsimp only [K, M0, M1, R]
    calc
      (Real.exp (-t) : ℂ) / ((t : ℂ) + z) =
        (Real.exp (-t) : ℂ) * (1 / ((t : ℂ) + z)) := by ring
      _ = (Real.exp (-t) : ℂ) *
        (1 / z - (t : ℂ) / z^2 + (t : ℂ)^2 / (z^2 * ((t : ℂ) + z))) := by
        rw [hkernel]
      _ = (1 / z) * (Real.exp (-t) : ℂ) -
        (1 / z^2) * ((Real.exp (-t) : ℂ) * (t : ℂ)) +
        (1 / z^2) *
          ((Real.exp (-t) : ℂ) * (t : ℂ)^2 / ((t : ℂ) + z)) := by
        field_simp [hz, htz]
  have hK :
    (∫ t : ℝ in Ioi 0, K t) =
      1 / z - 1 / z^2 + (1 / z^2) * ∫ t : ℝ in Ioi 0, R t := by
    rw [integral_congr_ae hK_ae]
    calc
      (∫ t : ℝ in Ioi 0,
        (1 / z) * M0 t - (1 / z^2) * M1 t + (1 / z^2) * R t) =
        (∫ t : ℝ in Ioi 0, (1 / z) * M0 t - (1 / z^2) * M1 t) +
          ∫ t : ℝ in Ioi 0, (1 / z^2) * R t := by
        exact integral_add ((hM0.const_mul _).sub (hM1.const_mul _)) (hR.const_mul _)
      _ = ((1 / z) * (∫ t : ℝ in Ioi 0, M0 t) -
        (1 / z^2) * (∫ t : ℝ in Ioi 0, M1 t)) +
        (1 / z^2) * ∫ t : ℝ in Ioi 0, R t := by
        rw [integral_sub (hM0.const_mul _) (hM1.const_mul _),
          integral_const_mul, integral_const_mul, integral_const_mul]
      _ = 1 / z - 1 / z^2 + (1 / z^2) * ∫ t : ℝ in Ioi 0, R t := by
        dsimp only [M0, M1]
        rw [show (∫ t : ℝ in Ioi 0, (Real.exp (-t) : ℂ)) = 1 by
          simpa using integral_complex_exp_moment 0,
          show (∫ t : ℝ in Ioi 0, (Real.exp (-t) : ℂ) * (t : ℂ)) = 1 by
            simpa using integral_complex_exp_moment 1]
        ring
  have hpartial :
    e1AsymptoticPartial 2 z hz =
      Complex.exp (-z) / z - Complex.exp (-z) / z^2 := by
    norm_num [e1AsymptoticPartial, e1AsymptoticPartialRaw, e1AsymptoticTerm,
      e1AsymptoticTermRaw, Finset.sum_range_succ]
    field_simp [hz]
    ring
  rw [e1AsymptoticRemainder, principal_e1_integral z hz harg]
  change Complex.exp (-z) * (∫ t : ℝ in Ioi 0, K t) - e1AsymptoticPartial 2 z hz =
    Complex.exp (-z) / z^2 * ∫ t : ℝ in Ioi 0, R t
  rw [hK, hpartial]
  field_simp [hz]
  ring

end Complex


-- created on 2026-10-20
-- updated on 2026-10-26
