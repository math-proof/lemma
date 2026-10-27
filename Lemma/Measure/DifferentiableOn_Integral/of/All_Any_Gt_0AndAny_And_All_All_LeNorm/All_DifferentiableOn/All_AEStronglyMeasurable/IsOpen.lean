import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory Metric Filter Topology


private lemma helper_main {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
  {U : Set ℂ} (hU : IsOpen U) (F : ℂ → Y → ℂ)
  (hmeas : ∀ z ∈ U, AEStronglyMeasurable (F z) ν)
  (hhol : ∀ a : Y, DifferentiableOn ℂ (fun z => F z a) U)
  (hdom : ∀ z₀ ∈ U, ∃ ε : ℝ, 0 < ε ∧ ∃ M : Y → ℝ, Integrable M ν ∧
    ∀ z ∈ Metric.ball z₀ ε, ∀ a : Y, ‖F z a‖ ≤ M a) :
  DifferentiableOn ℂ (fun z => ∫ a, F z a ∂ν) U := by
  intro z₀ hz₀
  obtain ⟨ε, hε, M, hM, hbd⟩ := hdom z₀ hz₀
  obtain ⟨δ₀, hδ₀, hballU⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  set δ : ℝ := min ε δ₀ / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have h2δε : 2 * δ ≤ ε := by rw [hδdef]; linarith [min_le_left ε δ₀]
  have h2δ₀ : 2 * δ ≤ δ₀ := by rw [hδdef]; linarith [min_le_right ε δ₀]
  have hBU : ball z₀ (2 * δ) ⊆ U := (ball_subset_ball h2δ₀).trans hballU
  have hBε : ball z₀ (2 * δ) ⊆ ball z₀ ε := ball_subset_ball h2δε
  set F' : ℂ → Y → ℂ := fun z a => deriv (fun w => F w a) z with hF'
  have hderiv : ∀ a : Y, ∀ z ∈ ball z₀ δ, HasDerivAt (fun w => F w a) (F' z a) z := by
    intro a z hz
    exact ((hhol a).differentiableAt (hU.mem_nhds (hBU (ball_subset_ball (by linarith) hz)))).hasDerivAt
  have hsub : ∀ z ∈ ball z₀ δ, closedBall z δ ⊆ ball z₀ (2 * δ) := by
    intro z hz w hw
    rw [mem_ball] at hz ⊢
    rw [mem_closedBall] at hw
    calc
      _ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
      _ < δ + δ := by linarith
      _ = 2 * δ := by ring
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (F := F) (F' := F') (x₀ := z₀)
    (bound := fun a => M a / δ) (ball_mem_nhds z₀ hδ)
    (Filter.eventually_of_mem (hU.mem_nhds hz₀) hmeas)
    (Integrable.mono' hM (hmeas z₀ hz₀) (Eventually.of_forall fun a => hbd z₀ (mem_ball_self hε) a))
    _
    _
    (hM.div_const δ)
    (Eventually.of_forall fun a z hz => hderiv a z hz)).2.differentiableAt.differentiableWithinAt
  set t : ℕ → ℂ := fun n => ((δ / ((n : ℝ) + 2) : ℝ) : ℂ) with ht
  have htpos : ∀ n : ℕ, 0 < δ / ((n : ℝ) + 2) := fun n => by positivity
  have ht_ne : ∀ n : ℕ, t n ≠ 0 := fun n => by
    show (((δ / ((n : ℝ) + 2) : ℝ)) : ℂ) ≠ 0
    exact_mod_cast (htpos n).ne'
  have ht_lt : ∀ n : ℕ, ‖t n‖ < δ := fun n => by
    show ‖((((δ / ((n : ℝ) + 2) : ℝ)) : ℂ))‖ < δ
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (htpos n), div_lt_iff₀ (by positivity)]
    nlinarith [hδ]
  have ht_mem : ∀ n : ℕ, z₀ + t n ∈ U := fun n =>
    hBU (by rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; linarith [ht_lt n])
  have ht0 : Tendsto t atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => δ / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
    rwa [Complex.ofReal_zero] at h2
  have ht0' : Tendsto t atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht0, Eventually.of_forall fun n => ht_ne n⟩
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n a => (t n)⁻¹ • (F (z₀ + t n) a - F z₀ a)) (fun n => ?_) ?_
  ·
    show AEStronglyMeasurable (fun a => (t n)⁻¹ • (F (z₀ + t n) a - F z₀ a)) ν
    exact ((hmeas _ (ht_mem n)).sub (hmeas z₀ hz₀)).const_smul ((t n)⁻¹)
  ·
    refine Eventually.of_forall fun a => ?_
    exact ((hderiv a z₀ (mem_ball_self hδ)).tendsto_slope_zero).comp ht0'
  apply Eventually.of_forall
  intro a z hz
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ ?_ ?_
  · exact ((hhol a).mono (closure_ball_subset_closedBall.trans ((hsub z hz).trans hBU))).diffContOnCl
  ·
    intro w hw
    exact hbd w (hBε (hsub z hz (sphere_subset_closedBall hw))) a
/--
[MeasureTheory_differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MeasureTheory_differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le.lean)
-/
@[path]
private lemma main
  [MeasurableSpace Y]
  {ν : Measure Y}
  {U : Set ℂ}
  {F : ℂ → Y → ℂ}
-- given
  (hU : IsOpen U)
  (hmeas : ∀ z ∈ U, AEStronglyMeasurable (F z) ν)
  (hhol : ∀ a : Y, DifferentiableOn ℂ (fun z => F z a) U)
  (hdom : ∀ z₀ ∈ U, ∃ ε : ℝ, 0 < ε ∧ ∃ M : Y → ℝ, Integrable M ν ∧ ∀ z ∈ Metric.ball z₀ ε, ∀ a : Y, ‖F z a‖ ≤ M a) :
-- imply
  DifferentiableOn ℂ (fun z => ∫ a, F z a ∂ν) U :=
-- proof
  helper_main ν hU F hmeas hhol hdom


-- created on 2026-10-23
