import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Probability.LevyKhintchin.Part17
open MeasureTheory
open scoped ENNReal NNReal MeasureTheory Topology
open MetaMathlibExt


namespace MetaMathlibExt

/--
[lkJump_of_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lkJump_of_abs_le (t : ℝ) {x : ℝ} (hx : |x| ≤ 1) :
  lkJump t x = Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) - 1 -
    Complex.I * (t : ℂ) * (x : ℂ) := by
  simp [lkJump, hx]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lkJump_of_one_lt_abs](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lkJump_of_one_lt_abs (t : ℝ) {x : ℝ} (hx : 1 < |x|) :
  lkJump t x = Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) - 1 := by
  simp [lkJump, not_le_of_gt hx]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lkJump_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lkJump_zero (t : ℝ) : lkJump t 0 = 0 := by
  simp [lkJump]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lkJump_zero_time](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lkJump_zero_time (x : ℝ) : lkJump 0 x = 0 := by
  simp [lkJump]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_norm_jump_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_norm_jump_le (t x : ℝ) :
  ‖lkJump t x‖ ≤ max 2 (t ^ 2 * Real.exp |t|) * min 1 (x ^ 2) := by
  by_cases hx : |x| ≤ 1
  · rw [lkJump_of_abs_le t hx, min_eq_right ((sq_le_one_iff_abs_le_one x).mpr hx)]
    let z : ℂ := Complex.I * (t : ℂ) * (x : ℂ)
    have hrem : ‖Complex.exp z - 1 - z‖ ≤ ‖z‖ ^ 2 * Real.exp ‖z‖ := by
      have h := Complex.norm_exp_sub_sum_le_norm_mul_exp z 2
      norm_num [Finset.sum_range_succ] at h
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
    rw [show Complex.I * (t : ℂ) * (x : ℂ) = z from rfl]
    calc
      ‖Complex.exp z - 1 - z‖ ≤ ‖z‖ ^ 2 * Real.exp ‖z‖ := hrem
      _ ≤ (|t| * |x|) ^ 2 * Real.exp |t| := by
        simp only [z, Complex.norm_mul, Complex.norm_I, Complex.norm_real, one_mul,
          Real.norm_eq_abs]
        gcongr
        exact mul_le_of_le_one_right (abs_nonneg t) hx
      _ = t ^ 2 * Real.exp |t| * x ^ 2 := by
        rw [mul_pow, sq_abs, sq_abs]
        ring
      _ ≤ max 2 (t ^ 2 * Real.exp |t|) * x ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg x)
  · have hx' : 1 < |x| := lt_of_not_ge hx
    rw [lkJump_of_one_lt_abs t hx', min_eq_left ((one_le_sq_iff_one_le_abs x).mpr hx'.le),
      mul_one]
    calc
      ‖Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) - 1‖
        ≤ ‖Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
        rw [show Complex.I * (t : ℂ) * (x : ℂ) = ((t * x : ℝ) : ℂ) * Complex.I by
          push_cast
          ring]
        rw [Complex.norm_exp_ofReal_mul_I]
        norm_num [Complex.norm_def]
      _ ≤ max 2 (t ^ 2 * Real.exp |t|) := le_max_left _ _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_norm_jump_le_of_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_norm_jump_le_of_abs_le {R t : ℝ} (hR : 0 ≤ R) (ht : |t| ≤ R) (x : ℝ) :
  ‖lkJump t x‖ ≤ max 2 (R ^ 2 * Real.exp R) * min 1 (x ^ 2) := by
  have h_sq : t ^ 2 ≤ R ^ 2 := by
    rw [← sq_abs t]
    exact (sq_le_sq₀ (abs_nonneg t) hR).2 ht
  have h_coeff : t ^ 2 * Real.exp |t| ≤ R ^ 2 * Real.exp R := by
    gcongr
  exact (lk_norm_jump_le t x).trans <|
    mul_le_mul_of_nonneg_right (max_le_max_left 2 h_coeff) (by positivity)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_jump_stronglyMeasurable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_jump_stronglyMeasurable (t : ℝ) : StronglyMeasurable (lkJump t) := by
  unfold lkJump
  have h_exp : StronglyMeasurable
    (fun x : ℝ ↦ Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) :=
    (by fun_prop : Continuous
      (fun x : ℝ ↦ Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)))).stronglyMeasurable
  have h_linear : StronglyMeasurable (fun x : ℝ ↦ Complex.I * (t : ℂ) * (x : ℂ)) :=
    (by fun_prop : Continuous (fun x : ℝ ↦ Complex.I * (t : ℂ) * (x : ℂ))).stronglyMeasurable
  exact (h_exp.sub stronglyMeasurable_const).sub <|
    h_linear.indicator <| (isClosed_le (by fun_prop) (by fun_prop)).measurableSet

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_moment_integrable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_moment_integrable {ν : Measure ℝ}
  (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) :
  Integrable (fun x : ℝ ↦ min 1 (x ^ 2)) ν := by
  have h_nonneg : 0 ≤ᵐ[ν] fun x : ℝ ↦ min 1 (x ^ 2) :=
    ae_of_all ν fun x ↦ by positivity
  have h_cont : Continuous (fun x : ℝ ↦ min 1 (x ^ 2)) := by fun_prop
  refine ⟨h_cont.stronglyMeasurable.aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal h_nonneg).2 hν

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_jump_integrable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_jump_integrable {ν : Measure ℝ}
  (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (t : ℝ) :
  Integrable (lkJump t) ν := by
  exact ((lk_moment_integrable hν).const_mul (max 2 (t ^ 2 * Real.exp |t|))).mono'
    (lk_jump_stronglyMeasurable t).aestronglyMeasurable
    (ae_of_all ν fun x ↦ lk_norm_jump_le t x)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_jump_integral_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_jump_integral_continuous {ν : Measure ℝ}
  (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) :
  Continuous (fun t : ℝ ↦ ∫ x, lkJump t x ∂ν) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  let R : ℝ := |t₀| + 1
  let C : ℝ := max 2 (R ^ 2 * Real.exp R)
  apply continuousAt_of_dominated (bound := fun x : ℝ ↦ C * min 1 (x ^ 2))
  · exact Filter.Eventually.of_forall fun t ↦
    (lk_jump_stronglyMeasurable t).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds t₀ zero_lt_one] with t ht
    have ht_dist : |t - t₀| < 1 := by simpa [Real.dist_eq] using ht
    have ht_abs : |t| ≤ R := by
      rw [show t = (t - t₀) + t₀ by ring]
      calc
        |t - t₀ + t₀| ≤ |t - t₀| + |t₀| := abs_add_le _ _
        _ ≤ R := by simp only [R]; linarith
    exact ae_of_all ν fun x ↦ lk_norm_jump_le_of_abs_le (by dsimp [R]; positivity) ht_abs x
  · exact (lk_moment_integrable hν).const_mul C
  · exact ae_of_all ν fun x ↦ by
    unfold lkJump
    by_cases hx : |x| ≤ 1
    · simp only [Set.indicator_of_mem (s := {y : ℝ | |y| ≤ 1}) hx]
      fun_prop
    · simp only [Set.indicator_of_notMem (s := {y : ℝ | |y| ≤ 1}) hx]
      fun_prop

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lkExponent_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lkExponent_zero (γ σ : ℝ) (ν : Measure ℝ) : lkExponent γ σ ν 0 = 0 := by
  simp [lkExponent]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_exponent_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_exponent_continuous {ν : Measure ℝ}
  (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (γ σ : ℝ) :
  Continuous (lkExponent γ σ ν) := by
  have h_int := lk_jump_integral_continuous hν
  unfold lkExponent
  fun_prop

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lkTruncationSet_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lkTruncationSet_measurable (k : ℕ) : MeasurableSet (lkTruncationSet k) :=
(isOpen_lt (by fun_prop) (by fun_prop)).measurableSet

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lkCutoff_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lkCutoff_tendsto_zero : Filter.Tendsto lkCutoff Filter.atTop (𝓝 0) := by
  have h :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
  exact h.congr' <| Filter.Eventually.of_forall fun k ↦ by rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_indicator_truncation_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_indicator_truncation_tendsto (t x : ℝ) :
  Filter.Tendsto
    (fun k : ℕ ↦ Set.indicator (lkTruncationSet k) (lkJump t) x)
    Filter.atTop (𝓝 (lkJump t x)) := by
  by_cases hx : x = 0
  · subst x
    refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun k ↦ ?_)
    by_cases h0 : 0 ∈ lkTruncationSet k
    · simp [Set.indicator_of_mem h0]
    · simp [Set.indicator_of_notMem h0]
  · have hxpos : 0 < |x| := abs_pos.mpr hx
    have hev : ∀ᶠ k : ℕ in Filter.atTop, lkCutoff k < |x| :=
      lkCutoff_tendsto_zero.eventually (gt_mem_nhds hxpos)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with k hk
    exact (Set.indicator_of_mem (f := lkJump t)
      (show x ∈ lkTruncationSet k from hk)).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lkConvPow_probability](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lkConvPow_probability (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (n : ℕ) :
  IsProbabilityMeasure (lkConvPow ρ n) := by
  induction n with
  | zero =>
    rw [lkConvPow]
    infer_instance
  | succ n ih =>
    rw [lkConvPow]
    infer_instance

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lkConvPow_succ_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lkConvPow_succ_iterate (ρ : Measure ℝ) [SFinite ρ] (n : ℕ) :
  lkConvPow ρ (n + 1) = Nat.iterate (Measure.conv ρ) n ρ := by
  induction n with
  | zero => simp [lkConvPow, Measure.conv_dirac_zero]
  | succ n ih =>
    rw [show n + 1 + 1 = (n + 1).succ from rfl, lkConvPow, ih]
    rw [show n + 1 = n.succ from rfl, Function.iterate_succ_apply']

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lkPoissonCoeff_toReal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lkPoissonCoeff_toReal (ρ : Measure ℝ) (n : ℕ) :
  (lkPoissonCoeff ρ n).toReal =
    Real.exp (-ρ.real Set.univ) / (n.factorial : ℝ) := by
  rw [lkPoissonCoeff, ENNReal.toReal_ofReal]
  positivity

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_integrable_exp_mul_I](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_integrable_exp_mul_I (ρ : Measure ℝ) [IsFiniteMeasure ρ] (t : ℝ) :
  Integrable (fun x : ℝ ↦ Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) ρ := by
  have h_cont : Continuous
    (fun x : ℝ ↦ Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) := by fun_prop
  refine Integrable.of_bound h_cont.stronglyMeasurable.aestronglyMeasurable 1 ?_
  exact ae_of_all ρ fun x ↦ by
    rw [show Complex.I * (t : ℂ) * (x : ℂ) = ((t * x : ℝ) : ℂ) * Complex.I by
      push_cast
      ring]
    rw [Complex.norm_exp_ofReal_mul_I]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_integral_compensation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_integral_compensation (ν : Measure ℝ) (k : ℕ) (t : ℝ) :
  (∫ x, Set.indicator {y : ℝ | |y| ≤ 1}
    (fun y ↦ Complex.I * (t : ℂ) * (y : ℂ)) x ∂lkTruncate ν k) =
    Complex.I * (t : ℂ) * (lkCompensation ν k : ℂ) := by
  have h_fun :
    (fun x : ℝ ↦ Set.indicator {y : ℝ | |y| ≤ 1}
      (fun y ↦ Complex.I * (t : ℂ) * (y : ℂ)) x) =
      fun x ↦ Complex.I * (t : ℂ) *
        ((Set.indicator {y : ℝ | |y| ≤ 1} (id : ℝ → ℝ) x : ℝ) : ℂ) := by
    funext x
    by_cases hx : |x| ≤ 1 <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  rw [h_fun, integral_const_mul, integral_complex_ofReal]
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lkVariance_coe](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lkVariance_coe (σ : ℝ) : (lkVariance σ : ℝ) = σ ^ 2 :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_integral_truncate_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_integral_truncate_tendsto {ν : Measure ℝ}
  (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (t : ℝ) :
  Filter.Tendsto (fun k : ℕ ↦ ∫ x, lkJump t x ∂lkTruncate ν k) Filter.atTop
    (𝓝 (∫ x, lkJump t x ∂ν)) := by
  let C : ℝ := max 2 (t ^ 2 * Real.exp |t|)
  have h_dc : Filter.Tendsto
    (fun k : ℕ ↦ ∫ x, Set.indicator (lkTruncationSet k) (lkJump t) x ∂ν)
    Filter.atTop (𝓝 (∫ x, lkJump t x ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x : ℝ ↦ C * min 1 (x ^ 2))
    · intro k
      exact ((lk_jump_stronglyMeasurable t).indicator
        (lkTruncationSet_measurable k)).aestronglyMeasurable
    · exact (lk_moment_integrable hν).const_mul C
    · intro k
      exact ae_of_all ν fun x ↦ by
        by_cases hx : x ∈ lkTruncationSet k
        · rw [Set.indicator_of_mem hx]
          exact lk_norm_jump_le t x
        · rw [Set.indicator_of_notMem hx, norm_zero]
          positivity
    · exact ae_of_all ν fun x ↦ lk_indicator_truncation_tendsto t x
  refine h_dc.congr' (Filter.Eventually.of_forall fun k ↦ ?_)
  simpa only [lkTruncate] using
    (integral_indicator (μ := ν) (f := lkJump t) (lkTruncationSet_measurable k))

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_exponent_truncate_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_exponent_truncate_tendsto {ν : Measure ℝ}
  (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (γ σ t : ℝ) :
  Filter.Tendsto (fun k : ℕ ↦ lkExponent γ σ (lkTruncate ν k) t) Filter.atTop
    (𝓝 (lkExponent γ σ ν t)) := by
  have h := (tendsto_const_nhds (x :=
    Complex.I * (γ : ℂ) * (t : ℂ) - (((σ ^ 2 * t ^ 2 : ℝ) : ℂ) / 2))).add
      (lk_integral_truncate_tendsto hν t)
  simpa only [lkExponent] using h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lkApproxPM_toMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lkApproxPM_toMeasure (γ σ : ℝ) (ν : Measure ℝ)
  (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (k : ℕ) :
  (lkApproxPM γ σ ν hν k : Measure ℝ) = lkTruncatedLaw γ σ ν k :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_root_moment](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_root_moment {ν : Measure ℝ}
  (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (n : ℕ) :
  ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂lkRootMeasure n ν < ∞ := by
  rw [lkRootMeasure, lintegral_smul_measure]
  change lkRootScale n * (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν) < ∞
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hν

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lkRootSigma_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lkRootSigma_sq (σ : ℝ) (n : ℕ) :
  lkRootSigma σ n ^ 2 = σ ^ 2 / (n : ℝ) :=
Real.sq_sqrt (div_nonneg (sq_nonneg σ) (Nat.cast_nonneg n))

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lkRootScale_toReal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lkRootScale_toReal (n : ℕ) :
  (lkRootScale n).toReal = (n : ℝ)⁻¹ :=
ENNReal.toReal_ofReal (inv_nonneg.mpr (Nat.cast_nonneg n))

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_root_exponent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_root_exponent (γ σ t : ℝ) (ν : Measure ℝ) {n : ℕ} (hn : n ≠ 0) :
  lkExponent (γ / (n : ℝ)) (lkRootSigma σ n) (lkRootMeasure n ν) t =
    lkExponent γ σ ν t / (n : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  unfold lkExponent lkRootMeasure
  rw [integral_smul_measure, lkRootScale_toReal, lkRootSigma_sq]
  simp only [Complex.real_smul]
  push_cast
  field_simp [hnR]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_exp_div_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_exp_div_pow (z : ℂ) {n : ℕ} (hn : n ≠ 0) :
  Complex.exp (z / (n : ℝ)) ^ n = Complex.exp z := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp [Nat.cast_ne_zero.mpr hn]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lkSymmetrize_probability](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lkSymmetrize_probability (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
  IsProbabilityMeasure (lkSymmetrize ρ) := by
  unfold lkSymmetrize
  infer_instance

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_charFun_symmetrize](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_charFun_symmetrize (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (t : ℝ) :
  charFun (lkSymmetrize ρ) t = ((‖charFun ρ t‖ ^ 2 : ℝ) : ℂ) := by
  unfold lkSymmetrize
  rw [charFun_conv, charFun_map_mul]
  rw [neg_one_mul, charFun_neg, Complex.mul_conj, Complex.normSq_eq_norm_sq]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_one_sub_cos_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_one_sub_cos_two_le (x : ℝ) :
  1 - Real.cos (2 * x) ≤ 4 * (1 - Real.cos x) := by
  rw [Real.cos_two_mul]
  nlinarith [sq_nonneg (Real.cos x - 1)]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_integrable_cos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_integrable_cos (ρ : Measure ℝ) [IsFiniteMeasure ρ] (t : ℝ) :
  Integrable (fun x : ℝ ↦ Real.cos (t * x)) ρ := by
  apply Integrable.of_bound (by fun_prop) 1
  exact ae_of_all ρ fun x ↦ by
    simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (t * x)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_re_charFun_eq_integral_cos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_re_charFun_eq_integral_cos (ρ : Measure ℝ) [IsFiniteMeasure ρ] (t : ℝ) :
  (charFun ρ t).re = ∫ x, Real.cos (t * x) ∂ρ := by
  rw [charFun_apply_real]
  have h_exp : Integrable
    (fun x : ℝ ↦ Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) ρ := by
    apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all ρ fun x ↦ by
      rw [show (t : ℂ) * (x : ℂ) * Complex.I = ((t * x : ℝ) : ℂ) * Complex.I by
        push_cast
        ring]
      rw [Complex.norm_exp_ofReal_mul_I]
  calc
    (∫ x, Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) ∂ρ).re =
      ∫ x, (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)).re ∂ρ := by
      exact (integral_re h_exp).symm
    _ = ∫ x, Real.cos (t * x) ∂ρ := by
      apply integral_congr_ae
      exact ae_of_all ρ fun x ↦ by
        change (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)).re = Real.cos (t * x)
        rw [show (t : ℂ) * (x : ℂ) * Complex.I = ((t * x : ℝ) : ℂ) * Complex.I by
          push_cast
          ring]
        exact Complex.exp_ofReal_mul_I_re (t * x)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_one_sub_re_charFun_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_one_sub_re_charFun_two_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
  (t : ℝ) :
  1 - (charFun ρ (2 * t)).re ≤ 4 * (1 - (charFun ρ t).re) := by
  rw [lk_re_charFun_eq_integral_cos, lk_re_charFun_eq_integral_cos]
  have hcos₂ := lk_integrable_cos ρ (2 * t)
  have hcos := lk_integrable_cos ρ t
  calc
    1 - ∫ x, Real.cos ((2 * t) * x) ∂ρ =
      ∫ x, (1 - Real.cos ((2 * t) * x)) ∂ρ := by
      rw [integral_sub (integrable_const 1) hcos₂]
      simp
    _ ≤ ∫ x, 4 * (1 - Real.cos (t * x)) ∂ρ := by
      apply integral_mono ((integrable_const 1).sub hcos₂)
        ((integrable_const 1).sub hcos |>.const_mul 4)
      intro x
      change 1 - Real.cos ((2 * t) * x) ≤ 4 * (1 - Real.cos (t * x))
      simpa only [mul_assoc] using lk_one_sub_cos_two_le (t * x)
    _ = 4 * (1 - ∫ x, Real.cos (t * x) ∂ρ) := by
      rw [integral_const_mul, integral_sub (integrable_const 1) hcos]
      simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_one_sub_norm_charFun_sq_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_one_sub_norm_charFun_sq_two_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
  (t : ℝ) :
  1 - ‖charFun ρ (2 * t)‖ ^ 2 ≤ 4 * (1 - ‖charFun ρ t‖ ^ 2) := by
  let _ := lkSymmetrize_probability ρ
  have h := lk_one_sub_re_charFun_two_le (lkSymmetrize ρ) t
  rw [lk_charFun_symmetrize, lk_charFun_symmetrize] at h
  simpa only [Complex.ofReal_re] using h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_rootsOfUnity_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_rootsOfUnity_finite {n : ℕ} (hn : n ≠ 0) :
  Set.Finite {z : ℂ | z ^ n = 1} := by
  let _ : NeZero n := ⟨hn⟩
  have hfin : Set.Finite
    (Set.range fun ζ : rootsOfUnity n ℂ ↦ (((ζ : ℂˣ) : ℂ))) := Set.finite_range _
  convert hfin using 1
  ext z
  constructor
  · intro hz
    exact ⟨rootsOfUnity.mkOfPowEq z hz, by simp⟩
  · rintro ⟨ζ, rfl⟩
    exact (mem_rootsOfUnity' n (ζ : ℂˣ)).mp ζ.property

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_charFun_root_eq_exp_div](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_charFun_root_eq_exp_div {μ ρ : Measure ℝ}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
  {L : ℝ → ℂ} (hL : Continuous L) (hL0 : L 0 = 0)
  (hLexp : ∀ t : ℝ, Complex.exp (L t) = charFun μ t)
  {n : ℕ} (hn : n ≠ 0)
  (hroot : ∀ t : ℝ, charFun μ t = charFun ρ t ^ n) :
  ∀ t : ℝ, charFun ρ t = Complex.exp (L t / (n : ℝ)) := by
  let q : ℝ → ℂ := fun t ↦ charFun ρ t / Complex.exp (L t / (n : ℝ))
  have hq : Continuous q := by
    unfold q
    have harg : Continuous (fun t : ℝ ↦ L t / (n : ℝ)) := by fun_prop
    have hden : Continuous (fun t : ℝ ↦ Complex.exp (L t / (n : ℝ))) :=
      (by fun_prop : Continuous Complex.exp).comp harg
    exact (MeasureTheory.continuous_charFun (μ := ρ)).div hden
      (fun t ↦ Complex.exp_ne_zero (L t / (n : ℝ)))
  have hmaps : Set.MapsTo q Set.univ {z : ℂ | z ^ n = 1} := by
    intro t _
    change q t ^ n = 1
    unfold q
    rw [div_pow, ← hroot t, lk_exp_div_pow _ hn, ← hLexp t]
    exact div_self (Complex.exp_ne_zero _)
  intro t
  have hconst := PreconnectedSpace.isPreconnected_univ.constant_of_mapsTo
    (lk_rootsOfUnity_finite hn).isDiscrete hq.continuousOn hmaps
    (Set.mem_univ t) (Set.mem_univ 0)
  have hq0 : q 0 = 1 := by simp [q, hL0]
  have hqt : q t = 1 := hconst.trans hq0
  exact (div_eq_one_iff_eq (Complex.exp_ne_zero (L t / (n : ℝ)))).mp hqt

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_nat_mul_exp_div_sub_one_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_nat_mul_exp_div_sub_one_tendsto (z : ℂ) :
  Filter.Tendsto
    (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ) *
      (Complex.exp (z / ((n + 1 : ℕ) : ℂ)) - 1))
    Filter.atTop (𝓝 z) := by
  by_cases hz : z = 0
  · subst z
    simp
  · let u : ℕ → ℂ := fun n ↦ z / ((n + 1 : ℕ) : ℂ)
    have hinv : Filter.Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℂ))⁻¹)
      Filter.atTop (𝓝 0) := by
      have h := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).comp
        (Filter.tendsto_add_atTop_nat 1)
      exact h.congr' <| Filter.Eventually.of_forall fun n ↦ by rfl
    have hu : Filter.Tendsto u Filter.atTop (𝓝 0) := by
      unfold u
      simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul hinv
    have hune : ∀ᶠ n : ℕ in Filter.atTop, u n ∈ ({0}ᶜ : Set ℂ) :=
      Filter.Eventually.of_forall fun n ↦ by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, u]
        exact div_ne_zero hz (by exact_mod_cast Nat.succ_ne_zero n)
    have hu' : Filter.Tendsto u Filter.atTop (𝓝[≠] (0 : ℂ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hu, hune⟩
    have hslope := (Complex.hasDerivAt_exp 0).tendsto_slope_zero.comp hu'
    have hmul := hslope.const_mul z
    have hmul' : Filter.Tendsto
      (fun n ↦ z * (u n)⁻¹ * (Complex.exp (u n) - 1)) Filter.atTop (𝓝 z) := by
      simpa only [Function.comp_apply, zero_add, Complex.exp_zero, smul_eq_mul,
        mul_assoc, mul_one] using hmul
    refine hmul'.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
    dsimp only [u, slope]
    have hn : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp [hz, hn]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_scaled_charFun_sub_one_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_scaled_charFun_sub_one_tendsto {ρ : ℕ → Measure ℝ} {L : ℝ → ℂ}
  (hρ : ∀ n t, charFun (ρ n) t = Complex.exp (L t / ((n + 1 : ℕ) : ℝ)))
  (t : ℝ) :
  Filter.Tendsto
    (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ) * (charFun (ρ n) t - 1))
    Filter.atTop (𝓝 (L t)) := by
  refine (lk_nat_mul_exp_div_sub_one_tendsto (L t)).congr'
    (Filter.Eventually.of_forall fun n ↦ ?_)
  dsimp only
  rw [hρ n t]
  push_cast
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_sinc_le_cos_half](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_sinc_le_cos_half {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
  Real.sinc x ≤ Real.cos (x / 2) := by
  obtain rfl | hx := hx0.eq_or_lt
  · simp
  rw [Real.sinc_of_ne_zero hx.ne']
  have hhalf0 : 0 ≤ x / 2 := by positivity
  have hhalfpi : x / 2 ≤ Real.pi / 2 := by linarith [Real.two_le_pi]
  have hcos : 0 ≤ Real.cos (x / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hhalfpi⟩
  have hsin : Real.sin (x / 2) ≤ x / 2 := Real.sin_le hhalf0
  have hid : Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    calc
      Real.sin x = Real.sin (2 * (x / 2)) := by congr 1; ring
      _ = 2 * Real.sin (x / 2) * Real.cos (x / 2) := Real.sin_two_mul _
  rw [hid]
  apply (div_le_iff₀ hx).2
  nlinarith

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_sq_div_32_le_one_sub_sinc_of_abs_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_sq_div_32_le_one_sub_sinc_of_abs_le_two {x : ℝ} (hx : |x| ≤ 2) :
  x ^ 2 / 32 ≤ 1 - Real.sinc x := by
  wlog hx0 : 0 ≤ x generalizing x
  · have hneg : 0 ≤ -x := neg_nonneg.mpr (le_of_not_ge hx0)
    have habs : |-x| ≤ 2 := by simpa using hx
    simpa [Real.sinc_neg] using this habs hneg
  have hsinc : Real.sinc x ≤ Real.cos (x / 2) :=
    lk_sinc_le_cos_half hx0 (by simpa [abs_of_nonneg hx0] using hx)
  have harg : |x / 2| ≤ Real.pi := by
    rw [abs_div]
    norm_num
    nlinarith [Real.two_le_pi]
  have hcos := Real.cos_le_one_sub_mul_cos_sq harg
  have hpi : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_le_four]
  have hpipos : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hcoeff : (1 : ℝ) / 32 ≤ 1 / (2 * Real.pi ^ 2) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  calc
    x ^ 2 / 32 = x ^ 2 * (1 / 32) := by ring
    _ ≤ x ^ 2 * (1 / (2 * Real.pi ^ 2)) :=
      mul_le_mul_of_nonneg_left hcoeff (sq_nonneg x)
    _ = 2 / Real.pi ^ 2 * (x / 2) ^ 2 := by
      field_simp [ne_of_gt Real.pi_pos]
    _ ≤ 1 - Real.cos (x / 2) := by linarith
    _ ≤ 1 - Real.sinc x := by linarith

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_scaled_exp_sub_one_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_scaled_exp_sub_one_bound (z : ℂ) (n : ℕ) :
  ‖((n + 1 : ℕ) : ℂ) * (Complex.exp (z / ((n + 1 : ℕ) : ℂ)) - 1)‖ ≤
    ‖z‖ * Real.exp ‖z‖ := by
  let d : ℝ := (n + 1 : ℕ)
  have hd : 0 < d := by dsimp [d]; positivity
  have hrem := Complex.norm_exp_sub_sum_le_norm_mul_exp (z / (d : ℂ)) 1
  norm_num [Finset.sum_range_succ] at hrem
  calc
    ‖((n + 1 : ℕ) : ℂ) * (Complex.exp (z / (d : ℂ)) - 1)‖ =
      d * ‖Complex.exp (z / (d : ℂ)) - 1‖ := by
        rw [Complex.norm_mul, Complex.norm_natCast]
    _ ≤ d * ((‖z‖ / d) * Real.exp (‖z‖ / d)) := by
      rw [abs_of_pos hd] at hrem
      exact mul_le_mul_of_nonneg_left hrem hd.le
    _ = ‖z‖ * Real.exp (‖z‖ / d) := by field_simp
    _ ≤ ‖z‖ * Real.exp ‖z‖ := by
      gcongr
      exact div_le_self (norm_nonneg z) (by dsimp [d]; norm_num)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_scaled_one_sub_charFun_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_scaled_one_sub_charFun_bound {ρ : Measure ℝ} {L : ℝ → ℂ}
  (n : ℕ) (hρ : ∀ t, charFun ρ t = Complex.exp (L t / ((n + 1 : ℕ) : ℝ)))
  (t : ℝ) :
  ‖((n + 1 : ℕ) : ℂ) * (1 - charFun ρ t)‖ ≤ ‖L t‖ * Real.exp ‖L t‖ := by
  rw [hρ t]
  have h := lk_scaled_exp_sub_one_bound (L t) n
  rw [show 1 - Complex.exp (L t / ((n + 1 : ℕ) : ℝ)) =
    -(Complex.exp (L t / ((n + 1 : ℕ) : ℂ)) - 1) by
      push_cast
      ring]
  simpa only [mul_neg, norm_neg] using h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_norm_integral_scaled_one_sub_charFun_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_norm_integral_scaled_one_sub_charFun_le {ρ : Measure ℝ} {L : ℝ → ℂ}
  (hL : Continuous L) (n : ℕ)
  (hρ : ∀ t, charFun ρ t = Complex.exp (L t / ((n + 1 : ℕ) : ℝ)))
  (a b : ℝ) (hab : a ≤ b) :
  ‖∫ t : ℝ in a..b, ((n + 1 : ℕ) : ℂ) * (1 - charFun ρ t)‖ ≤
    ∫ t : ℝ in a..b, ‖L t‖ * Real.exp ‖L t‖ := by
  apply intervalIntegral.norm_integral_le_of_norm_le hab
  · exact Filter.Eventually.of_forall fun t _ ↦ lk_scaled_one_sub_charFun_bound n hρ t
  · exact (by fun_prop : Continuous fun t ↦ ‖L t‖ * Real.exp ‖L t‖).intervalIntegrable _ _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_integral_one_sub_charFun](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_integral_one_sub_charFun (ρ : Measure ℝ) (hρ : IsProbabilityMeasure ρ) :
  ∫ t : ℝ in (-1)..1, (1 - charFun ρ t) =
    (2 : ℂ) * ((∫ x : ℝ, 1 - Real.sinc x ∂ρ : ℝ) : ℂ) := by
  rw [intervalIntegral.integral_sub]
  · rw [integral_charFun_Icc (μ := ρ) (r := 1) (by norm_num)]
    simp only [one_mul]
    rw [integral_sub (integrable_const _) Real.integrable_sinc]
    norm_num
    ring
  · exact intervalIntegrable_const
  · exact (continuous_charFun (μ := ρ)).intervalIntegrable _ _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_integral_one_sub_sinc_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_integral_one_sub_sinc_nonneg (ρ : Measure ℝ) :
  0 ≤ ∫ x : ℝ, 1 - Real.sinc x ∂ρ :=
  integral_nonneg fun x ↦ sub_nonneg.mpr (Real.sinc_le_one x)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_scaled_sinc_integral_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_scaled_sinc_integral_le {ρ : Measure ℝ} {L : ℝ → ℂ}
  (hprob : IsProbabilityMeasure ρ) (hL : Continuous L) (n : ℕ)
  (hρ : ∀ t, charFun ρ t = Complex.exp (L t / ((n + 1 : ℕ) : ℝ))) :
  (n + 1 : ℝ) * ∫ x : ℝ, 1 - Real.sinc x ∂ρ ≤
    (1 / 2 : ℝ) * ∫ t : ℝ in (-1)..1, ‖L t‖ * Real.exp ‖L t‖ := by
  have hnorm := lk_norm_integral_scaled_one_sub_charFun_le hL n hρ (-1) 1 (by norm_num)
  have heq : (∫ t : ℝ in (-1)..1,
    ((n + 1 : ℕ) : ℂ) * (1 - charFun ρ t)) =
    ((n + 1 : ℕ) : ℂ) * ((2 : ℂ) *
      ((∫ x : ℝ, 1 - Real.sinc x ∂ρ : ℝ) : ℂ)) := by
    rw [intervalIntegral.integral_const_mul]
    rw [lk_integral_one_sub_charFun ρ hprob]
  rw [heq] at hnorm
  have hnon := lk_integral_one_sub_sinc_nonneg ρ
  simp only [Complex.norm_mul, Complex.norm_natCast, Complex.norm_two, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hnon] at hnorm
  push_cast at hnorm
  nlinarith

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_coe_canonicalWeightNN](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_coe_canonicalWeightNN (x : ℝ) :
  (lkCanonicalWeightNN x : ℝ) = lkCanonicalWeight x :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_canonicalIntegrand_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_canonicalIntegrand_zero (t : ℝ) :
  lkCanonicalIntegrand t 0 = -((t : ℂ) ^ 2) / 2 := by
  simp [lkCanonicalIntegrand]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_tendsto_integral_canonicalIntegrand](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_tendsto_integral_canonicalIntegrand
  {M : ℕ → FiniteMeasure ℝ} {K : FiniteMeasure ℝ} {F : Filter ℕ}
  (hM : Filter.Tendsto M F (nhds K)) (t : ℝ) :
  Filter.Tendsto
    (fun n ↦ ∫ x, lkCanonicalIntegrand t x ∂(M n : Measure ℝ)) F
    (nhds (∫ x, lkCanonicalIntegrand t x ∂(K : Measure ℝ))) := by
  have hre := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hM)
    (lkCanonicalIntegrandReBCF t)
  have him := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hM)
    (lkCanonicalIntegrandImBCF t)
  have hsum := hre.ofReal.add (him.ofReal.mul_const Complex.I)
  convert hsum using 1
  · funext n
    change (∫ x, lkCanonicalIntegrand t x ∂(M n : Measure ℝ)) =
      ((∫ x, (lkCanonicalIntegrand t x).re ∂(M n : Measure ℝ) : ℝ) : ℂ) +
        (∫ x, (lkCanonicalIntegrand t x).im ∂(M n : Measure ℝ) : ℝ) * Complex.I
    exact (integral_re_add_im
      ((lkCanonicalIntegrandBCF t).integrable (M n : Measure ℝ))).symm
  · congr 1
    change (∫ x, lkCanonicalIntegrand t x ∂(K : Measure ℝ)) =
      ((∫ x, (lkCanonicalIntegrand t x).re ∂(K : Measure ℝ) : ℝ) : ℂ) +
        (∫ x, (lkCanonicalIntegrand t x).im ∂(K : Measure ℝ) : ℝ) * Complex.I
    exact (integral_re_add_im
      ((lkCanonicalIntegrandBCF t).integrable (K : Measure ℝ))).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_smoothTruncation_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_smoothTruncation_continuous : Continuous lkSmoothTruncation := by
  unfold lkSmoothTruncation
  exact continuous_id.div₀ (continuous_const.add (continuous_id.pow 2)) fun x ↦ by positivity

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_abs_smoothTruncation_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_abs_smoothTruncation_le_one (x : ℝ) :
  |lkSmoothTruncation x| ≤ 1 := by
  unfold lkSmoothTruncation
  rw [abs_div, abs_of_nonneg (by positivity : 0 ≤ 1 + x ^ 2)]
  apply (div_le_iff₀ (by positivity : 0 < 1 + x ^ 2)).2
  nlinarith [abs_nonneg x, sq_abs x]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_smoothTruncation_integrable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_smoothTruncation_integrable (rho : Measure ℝ) [IsFiniteMeasure rho] :
  Integrable lkSmoothTruncation rho := by
  apply Integrable.of_bound lk_smoothTruncation_continuous.aestronglyMeasurable 1
  exact ae_of_all rho fun x ↦ by
    simpa only [Real.norm_eq_abs, norm_one] using lk_abs_smoothTruncation_le_one x

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_smoothJump_integrable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_smoothJump_integrable (rho : Measure ℝ) [IsFiniteMeasure rho] (t : ℝ) :
  Integrable (lkSmoothJump t) rho := by
  have hlinear : Integrable
    (fun x ↦ Complex.I * (t : ℂ) * (lkSmoothTruncation x : ℂ)) rho :=
    (lk_smoothTruncation_integrable rho).ofReal.const_mul (Complex.I * (t : ℂ))
  have hlinear' : Integrable
    (fun x : ℝ ↦ Complex.I * (t : ℂ) * (x : ℂ) /
      ((1 + x ^ 2 : ℝ) : ℂ)) rho := by
    convert hlinear using 1
    funext x
    unfold lkSmoothTruncation
    push_cast
    ring
  exact ((lk_integrable_exp_mul_I rho t).sub (integrable_const 1)).sub hlinear'

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_inverseCanonicalWeight_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_inverseCanonicalWeight_measurable :
  Measurable lkInverseCanonicalWeight := by
  unfold lkInverseCanonicalWeight
  apply Measurable.ite (by simpa only [Set.ofPred_eq_eq_singleton] using
    (measurableSet_singleton (0 : ℝ)))
  · exact measurable_const
  · exact Measurable.ennreal_ofReal
    ((measurable_const.add (measurable_id.pow_const 2)).div (measurable_id.pow_const 2))

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_inverseCanonicalWeight_lt_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_inverseCanonicalWeight_lt_top (x : ℝ) :
  lkInverseCanonicalWeight x < ∞ := by
  unfold lkInverseCanonicalWeight
  split_ifs
  · exact ENNReal.zero_lt_top
  · exact ENNReal.ofReal_lt_top

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_moment_mul_inverseCanonicalWeight_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_moment_mul_inverseCanonicalWeight_le (x : ℝ) :
  lkInverseCanonicalWeight x * ENNReal.ofReal (min 1 (x ^ 2)) ≤ 2 := by
  by_cases hx : x = 0
  · subst x
    simp [lkInverseCanonicalWeight]
  simp only [lkInverseCanonicalWeight, hx, ↓reduceIte]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (1 + x ^ 2) / x ^ 2)]
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
  apply ENNReal.ofReal_le_ofReal
  by_cases hx1 : x ^ 2 ≤ 1
  · rw [min_eq_right hx1]
    have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
    field_simp
    linarith [sq_nonneg x]
  · rw [min_eq_left (le_of_not_ge hx1)]
    have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    rw [mul_one]
    apply (div_le_iff₀ hx2).2
    nlinarith

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_levyMeasure_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_levyMeasure_zero (K : FiniteMeasure ℝ) :
  lkLevyMeasure K {0} = 0 := by
  rw [lkLevyMeasure, withDensity_apply _ (measurableSet_singleton 0)]
  simp [lkInverseCanonicalWeight]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_levyMeasure_moment](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_levyMeasure_moment (K : FiniteMeasure ℝ) :
  (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂lkLevyMeasure K) < ∞ := by
  rw [lkLevyMeasure, lintegral_withDensity_eq_lintegral_mul _
    lk_inverseCanonicalWeight_measurable
    (by fun_prop : Measurable fun x : ℝ ↦ ENNReal.ofReal (min 1 (x ^ 2)))]
  calc
    (∫⁻ x, (lkInverseCanonicalWeight *
      fun x : ℝ ↦ ENNReal.ofReal (min 1 (x ^ 2))) x ∂(K : Measure ℝ)) ≤
      ∫⁻ _ : ℝ, (2 : ℝ≥0∞) ∂(K : Measure ℝ) :=
      lintegral_mono lk_moment_mul_inverseCanonicalWeight_le
    _ < ∞ := by
      rw [lintegral_const]
      exact ENNReal.mul_lt_top (by norm_num) (measure_lt_top (K : Measure ℝ) Set.univ)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_inverseCanonicalWeight_toReal_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_inverseCanonicalWeight_toReal_of_ne {x : ℝ} (hx : x ≠ 0) :
  (lkInverseCanonicalWeight x).toReal = (1 + x ^ 2) / x ^ 2 := by
  simp only [lkInverseCanonicalWeight, hx, ↓reduceIte]
  rw [ENNReal.toReal_ofReal]
  positivity

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_abs_driftCorrection_le_moment](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_abs_driftCorrection_le_moment (x : ℝ) :
  |lkDriftCorrection x| ≤ min 1 (x ^ 2) := by
  by_cases hx : |x| ≤ 1
  · rw [min_eq_right ((sq_le_one_iff_abs_le_one x).2 hx)]
    rw [lkDriftCorrection, Set.indicator_of_mem
      (show x ∈ {y : ℝ | |y| ≤ 1} from hx)]
    change |x - x / (1 + x ^ 2)| ≤ x ^ 2
    rw [show x - x / (1 + x ^ 2) = x ^ 3 / (1 + x ^ 2) by
      field_simp
      ring]
    rw [abs_div, abs_pow, abs_of_nonneg (by positivity : 0 ≤ 1 + x ^ 2)]
    apply (div_le_iff₀ (by positivity : 0 < 1 + x ^ 2)).2
    rw [← sq_abs x]
    nlinarith [abs_nonneg x, sq_nonneg (|x| ^ 2)]
  · have hx' : 1 < |x| := lt_of_not_ge hx
    rw [min_eq_left ((one_le_sq_iff_one_le_abs x).2 hx'.le)]
    rw [lkDriftCorrection, Set.indicator_of_notMem
      (show x ∉ {y : ℝ | |y| ≤ 1} from hx), zero_sub, abs_neg]
    exact lk_abs_smoothTruncation_le_one x

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_driftCorrection_stronglyMeasurable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_driftCorrection_stronglyMeasurable :
  StronglyMeasurable lkDriftCorrection := by
  unfold lkDriftCorrection
  exact (stronglyMeasurable_id.indicator
    ((isClosed_le (by fun_prop) (by fun_prop)).measurableSet)).sub
      lk_smoothTruncation_continuous.stronglyMeasurable

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_driftCorrection_integrable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_driftCorrection_integrable {nu : Measure ℝ}
  (hnu : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂nu < ∞) :
  Integrable lkDriftCorrection nu := by
  exact (lk_moment_integrable hnu).mono'
    lk_driftCorrection_stronglyMeasurable.aestronglyMeasurable
    (ae_of_all nu fun x ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ min 1 (x ^ 2))]
        using lk_abs_driftCorrection_le_moment x)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_smoothJump_eq_jump_add_correction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_smoothJump_eq_jump_add_correction (t x : ℝ) :
  lkSmoothJump t x = Complex.I * (t : ℂ) * (lkDriftCorrection x : ℂ) +
    lkJump t x := by
  unfold lkSmoothJump lkJump lkDriftCorrection lkSmoothTruncation
  by_cases hx : |x| ≤ 1
  · simp only [Set.indicator_of_mem (s := {y : ℝ | |y| ≤ 1}) hx, id_eq]
    push_cast
    ring
  · simp only [Set.indicator_of_notMem (s := {y : ℝ | |y| ≤ 1}) hx]
    push_cast
    ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_integral_smoothJump_eq_jump_add_correction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_integral_smoothJump_eq_jump_add_correction {nu : Measure ℝ}
  (hnu : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂nu < ∞) (t : ℝ) :
  (∫ x, lkSmoothJump t x ∂nu) =
    Complex.I * (t : ℂ) * (∫ x, lkDriftCorrection x ∂nu : ℝ) +
      ∫ x, lkJump t x ∂nu := by
  have hlinear : Complex.I * (t : ℂ) * (∫ x, lkDriftCorrection x ∂nu : ℝ) =
    ∫ x, Complex.I * (t : ℂ) * (lkDriftCorrection x : ℂ) ∂nu := by
    rw [integral_const_mul, integral_complex_ofReal]
  rw [hlinear]
  calc
    (∫ x, lkSmoothJump t x ∂nu) =
      ∫ x, Complex.I * (t : ℂ) * (lkDriftCorrection x : ℂ) + lkJump t x ∂nu := by
      apply integral_congr_ae
      exact ae_of_all nu fun x ↦ lk_smoothJump_eq_jump_add_correction t x
    _ = _ := integral_add
      ((lk_driftCorrection_integrable hnu).ofReal.const_mul (Complex.I * (t : ℂ)))
      (lk_jump_integrable hnu t)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_gaussianCoefficient_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_gaussianCoefficient_nonneg (K : FiniteMeasure ℝ) :
  0 ≤ lkGaussianCoefficient K :=
  Real.sqrt_nonneg _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lk_gaussianCoefficient_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma lk_gaussianCoefficient_sq (K : FiniteMeasure ℝ) :
  lkGaussianCoefficient K ^ 2 = (K : Measure ℝ).real {0} :=
Real.sq_sqrt (measureReal_nonneg)

end MetaMathlibExt

/--
[levy_Khintchin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean)
-/
@[path]
private lemma levy_Khintchin_eq
  :
-- imply
  ∀ (μ : MeasureTheory.Measure ℝ), MeasureTheory.IsProbabilityMeasure μ →
    ((∀ n : ℕ, n ≠ 0 →
    ∃ ν : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure ν ∧
    μ = Nat.iterate (MeasureTheory.Measure.conv ν) (n - 1) ν) ↔
    ∃ γ : ℝ, ∃ σ : ℝ, 0 ≤ σ ∧
    ∃ ν : MeasureTheory.Measure ℝ,
    ν {0} = 0 ∧ (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) ∧
    ∀ t : ℝ, MeasureTheory.charFun μ t =
    Complex.exp ((Complex.I * (γ : ℂ) * (t : ℂ) -
    (((σ ^ 2 * t ^ 2 : ℝ) : ℂ) / 2) +
    ∫ x, (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) - 1 -
    Set.indicator {y : ℝ | |y| ≤ 1}
    (fun y => Complex.I * (t : ℂ) * (y : ℂ)) x) ∂ν))) := by
-- proof
  apply MetaMathlibExt.levy_Khintchin


-- created on 2026-10-20
-- updated on 2026-10-26
