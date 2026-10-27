import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.DifferentialAnalysis.code.ConvolutionSchwartzDeriv
open MeasureTheory Filter Topology Metric Set ConvolutionDensity
open scoped ZeroAtInfty ContDiff


namespace ConvolutionDensity

/--
[integrable_one_add_norm_sub_rpow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionSchwartzDeriv.lean)
-/
@[path]
lemma integrable_one_add_norm_sub_rpow
  {n : ℕ}
  {x₀ : EuclideanSpace ℝ (Fin n)} :
-- imply
  Integrable (fun y : EuclideanSpace ℝ (Fin n) => (1 + ‖x₀ - y‖) ^ (-(↑n + 1 : ℝ))) volume := by
-- proof
  exact (integrable_one_add_norm (E := EuclideanSpace ℝ (Fin n))
    (μ := volume) (r := ↑n + 1) (by simp [EuclideanSpace])).comp_sub_left x₀

end ConvolutionDensity

namespace ConvolutionDensity

/--
[schwartz_norm_le_of_mem_ball](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionSchwartzDeriv.lean)
-/
@[path]
lemma schwartz_norm_le_of_mem_ball
  {n : ℕ}
  {φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n) →L[ℝ] ℂ)}
  {x₀ x y : EuclideanSpace ℝ (Fin n)}
-- given
  (hx : x ∈ ball x₀ 1) :
-- imply
  ‖(φ : _ → _) (x - y)‖ ≤ (SchwartzMap.seminorm ℝ 0 0 φ + SchwartzMap.seminorm ℝ (n + 1) 0 φ) * 3 ^ (n + 1) * (1 + ‖x₀ - y‖) ^ (-(↑n + 1 : ℝ)) := by
-- proof
  set M := SchwartzMap.seminorm ℝ 0 0 φ
  set S := SchwartzMap.seminorm ℝ (n + 1) 0 φ
  have hM : ‖(φ : _ → _) (x - y)‖ ≤ M := SchwartzMap.norm_le_seminorm ℝ φ (x - y)
  have hS : ‖x - y‖ ^ (n + 1) * ‖(φ : _ → _) (x - y)‖ ≤ S := by
    have := SchwartzMap.le_seminorm ℝ (n + 1) 0 φ (x - y)
    simpa using this
  have h_pos : (0 : ℝ) < 1 + ‖x₀ - y‖ := by positivity
  have hx_norm : ‖x₀ - x‖ < 1 := by
    rw [mem_ball, dist_eq_norm] at hx
    rwa [norm_sub_rev] at hx
  have htri : ‖x₀ - y‖ ≤ ‖x₀ - x‖ + ‖x - y‖ := by
    calc ‖x₀ - y‖ = ‖(x₀ - x) + (x - y)‖ := by congr 1; abel
      _ ≤ ‖x₀ - x‖ + ‖x - y‖ := norm_add_le _ _
  have hrpow : (1 + ‖x₀ - y‖) ^ (-(↑n + 1 : ℝ)) = ((1 + ‖x₀ - y‖) ^ (n + 1))⁻¹ := by
    rw [show (-(↑n + 1 : ℝ)) = -(↑(n + 1) : ℝ) from by push_cast; ring]
    rw [Real.rpow_neg h_pos.le, Real.rpow_natCast]
  rw [hrpow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos h_pos _)]
  by_cases hxy : ‖x - y‖ ≤ 1
  ·
    have h3 : 1 + ‖x₀ - y‖ ≤ 3 := by linarith
    calc ‖(φ : _ → _) (x - y)‖ * (1 + ‖x₀ - y‖) ^ (n + 1)
      ≤ M * (3 : ℝ) ^ (n + 1) :=
        mul_le_mul hM (pow_le_pow_left₀ h_pos.le h3 _) (by positivity) (by positivity)
      _ ≤ (M + S) * (3 : ℝ) ^ (n + 1) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)
  ·
    push Not at hxy
    have hxy_pos : (0 : ℝ) < ‖x - y‖ := by linarith
    have h3xy : 1 + ‖x₀ - y‖ ≤ 3 * ‖x - y‖ := by nlinarith
    calc ‖(φ : _ → _) (x - y)‖ * (1 + ‖x₀ - y‖) ^ (n + 1)
      ≤ ‖(φ : _ → _) (x - y)‖ * (3 * ‖x - y‖) ^ (n + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h3xy _) (norm_nonneg _)
      _ = 3 ^ (n + 1) * (‖x - y‖ ^ (n + 1) * ‖(φ : _ → _) (x - y)‖) := by
        rw [mul_pow]; ring
      _ ≤ 3 ^ (n + 1) * S :=
        mul_le_mul_of_nonneg_left hS (by positivity)
      _ ≤ (M + S) * (3 : ℝ) ^ (n + 1) := by
        nlinarith [apply_nonneg (SchwartzMap.seminorm ℝ 0 0) φ,
          pow_nonneg (show (0:ℝ) ≤ 3 from by norm_num) (n+1)]
set_option maxHeartbeats 400000 in

end ConvolutionDensity

namespace ConvolutionDensity

/--
[schwartz_norm_le_of_mem_ball_gen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionSchwartzDeriv.lean)
-/
@[path]
lemma schwartz_norm_le_of_mem_ball_gen
  {n : ℕ}
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  {φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) F}
  {x₀ x y : EuclideanSpace ℝ (Fin n)}
-- given
  (hx : x ∈ ball x₀ 1) :
-- imply
  ‖(φ : _ → _) (x - y)‖ ≤ (SchwartzMap.seminorm ℝ 0 0 φ + SchwartzMap.seminorm ℝ (n + 1) 0 φ) * 3 ^ (n + 1) * (1 + ‖x₀ - y‖) ^ (-(↑n + 1 : ℝ)) := by
-- proof
  set M := SchwartzMap.seminorm ℝ 0 0 φ
  set S := SchwartzMap.seminorm ℝ (n + 1) 0 φ
  have hM : ‖(φ : _ → _) (x - y)‖ ≤ M := SchwartzMap.norm_le_seminorm ℝ φ (x - y)
  have hS : ‖x - y‖ ^ (n + 1) * ‖(φ : _ → _) (x - y)‖ ≤ S := by
    have := SchwartzMap.le_seminorm ℝ (n + 1) 0 φ (x - y); simpa using this
  have h_pos : (0 : ℝ) < 1 + ‖x₀ - y‖ := by positivity
  have hx_norm : ‖x₀ - x‖ < 1 := by rw [mem_ball, dist_eq_norm] at hx; rwa [norm_sub_rev] at hx
  have htri : ‖x₀ - y‖ ≤ ‖x₀ - x‖ + ‖x - y‖ := by
    calc ‖x₀ - y‖ = ‖(x₀ - x) + (x - y)‖ := by congr 1; abel
      _ ≤ ‖x₀ - x‖ + ‖x - y‖ := norm_add_le _ _
  have hrpow : (1 + ‖x₀ - y‖) ^ (-(↑n + 1 : ℝ)) = ((1 + ‖x₀ - y‖) ^ (n + 1))⁻¹ := by
    rw [show (-(↑n + 1 : ℝ)) = -(↑(n + 1) : ℝ) from by push_cast; ring]
    rw [Real.rpow_neg h_pos.le, Real.rpow_natCast]
  rw [hrpow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos h_pos _)]
  by_cases hxy : ‖x - y‖ ≤ 1
  · have h3 : 1 + ‖x₀ - y‖ ≤ 3 := by linarith
    calc ‖(φ : _ → _) (x - y)‖ * (1 + ‖x₀ - y‖) ^ (n + 1)
      ≤ M * 3 ^ (n + 1) :=
        mul_le_mul hM (pow_le_pow_left₀ h_pos.le h3 _) (by positivity) (by positivity)
      _ ≤ (M + S) * 3 ^ (n + 1) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)
  · push Not at hxy
    have hM_nn : (0 : ℝ) ≤ M := apply_nonneg _ _
    have h3xy : 1 + ‖x₀ - y‖ ≤ 3 * ‖x - y‖ := by nlinarith
    calc ‖(φ : _ → _) (x - y)‖ * (1 + ‖x₀ - y‖) ^ (n + 1)
      ≤ ‖(φ : _ → _) (x - y)‖ * (3 * ‖x - y‖) ^ (n + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h3xy _) (norm_nonneg _)
      _ = 3 ^ (n + 1) * (‖x - y‖ ^ (n + 1) * ‖(φ : _ → _) (x - y)‖) := by rw [mul_pow]; ring
      _ ≤ 3 ^ (n + 1) * S := mul_le_mul_of_nonneg_left hS (by positivity)
      _ ≤ (M + S) * 3 ^ (n + 1) := by
        nlinarith [pow_nonneg (show (0:ℝ) ≤ 3 from by norm_num) (n+1)]
set_option maxHeartbeats 800000 in

end ConvolutionDensity

namespace ConvolutionDensity

/--
[hasFDerivAt_smul_convolution_schwartz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionSchwartzDeriv.lean)
-/
@[path]
lemma hasFDerivAt_smul_convolution_schwartz
  {n : ℕ}
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [NormedSpace ℂ F]
  [SMulCommClass ℝ ℂ F]
  [SecondCountableTopology F]
  {v : C₀(EuclideanSpace ℝ (Fin n), ℂ)}
  {ψ : SchwartzMap (EuclideanSpace ℝ (Fin n)) F}
  {x₀₀ : EuclideanSpace ℝ (Fin n)} :
-- imply
  HasFDerivAt (fun x => ∫ y, v y • (ψ : _ → _) (x - y) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) (∫ y, v y • (SchwartzMap.fderivCLM ℝ _ F ψ : _ → _) (x₀₀ - y) ∂volume) x₀₀ := by
-- proof
  set ψ' := SchwartzMap.fderivCLM ℝ (EuclideanSpace ℝ (Fin n)) F ψ
  set C₀_bound := (SchwartzMap.seminorm ℝ 0 0 ψ' +
    SchwartzMap.seminorm ℝ (n + 1) 0 ψ') * 3 ^ (n + 1)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (F := fun x y => v y • (ψ : _ → _) (x - y))
    (F' := fun x y => v y • (ψ' : _ → _) (x - y))
    (bound := fun y => ‖v.toBCF‖ * (C₀_bound * (1 + ‖x₀₀ - y‖) ^ (-(↑n + 1 : ℝ))))
    (s := ball x₀₀ 1) (ball_mem_nhds x₀₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · apply Eventually.of_forall; intro x
    exact v.continuous.aestronglyMeasurable.smul
      (ψ.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · have hψ_int := ψ.integrable.comp_sub_left (μ := volume) x₀₀
    exact (hψ_int.norm.const_mul ‖v.toBCF‖).mono'
      (v.continuous.aestronglyMeasurable.smul
        (ψ.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (ae_of_all _ fun y => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (v.toBCF.norm_coe_le_norm y) (norm_nonneg _))
  · exact v.continuous.aestronglyMeasurable.smul
    (ψ'.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · filter_upwards with y; intro x hx; rw [norm_smul]
    calc ‖v y‖ * ‖(ψ' : _ → _) (x - y)‖
      ≤ ‖v.toBCF‖ * ‖(ψ' : _ → _) (x - y)‖ :=
        mul_le_mul (v.toBCF.norm_coe_le_norm y) le_rfl (norm_nonneg _) (norm_nonneg _)
      _ ≤ ‖v.toBCF‖ * (C₀_bound * (1 + ‖x₀₀ - y‖) ^ (-(↑n + 1 : ℝ))) :=
        mul_le_mul_of_nonneg_left (schwartz_norm_le_of_mem_ball_gen ψ' x₀₀ x y hx) (norm_nonneg _)
  · have := (integrable_one_add_norm_sub_rpow x₀₀).const_mul (‖v.toBCF‖ * C₀_bound)
    convert this using 1; ext y; ring
  · apply ae_of_all; intro y x _
    have hψ_at := ψ.hasFDerivAt (x - y)
    have hsub : HasFDerivAt (fun x' => x' - y)
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) x := by
      have h3 := (hasFDerivAt_id (𝕜 := ℝ) x).sub (hasFDerivAt_const (𝕜 := ℝ) y x)
      simp only [sub_zero] at h3; exact h3
    have hcomp := hψ_at.comp x hsub
    simp only [ContinuousLinearMap.comp_id, Function.comp_def] at hcomp
    exact hcomp.const_smul (v y)
set_option maxHeartbeats 800000 in

end ConvolutionDensity

namespace ConvolutionDensity

/--
[contDiff_smul_convolution_schwartz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionSchwartzDeriv.lean)
-/
@[path]
lemma contDiff_smul_convolution_schwartz
  {n : ℕ}
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [NormedSpace ℂ F]
  [SMulCommClass ℝ ℂ F]
  [SecondCountableTopology F]
  {v : C₀(EuclideanSpace ℝ (Fin n), ℂ)}
  {ψ : SchwartzMap (EuclideanSpace ℝ (Fin n)) F}
  {k : ℕ} :
-- imply
  ContDiff ℝ k (fun x => ∫ y, v y • (ψ : _ → _) (x - y) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
-- proof
  induction k generalizing F with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    apply continuous_iff_continuousAt.mpr; intro x₀
    apply continuousAt_of_dominated
      (bound := fun y => ‖v.toBCF‖ *
        ((SchwartzMap.seminorm ℝ 0 0 ψ + SchwartzMap.seminorm ℝ (n + 1) 0 ψ) *
        3 ^ (n + 1) * (1 + ‖x₀ - y‖) ^ (-(↑n + 1 : ℝ))))
    · apply Eventually.of_forall; intro x
      exact v.continuous.aestronglyMeasurable.smul
        (ψ.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    · apply Filter.Eventually.mono (ball_mem_nhds x₀ one_pos)
      intro x hx
      apply ae_of_all; intro y
      rw [norm_smul]
      exact mul_le_mul (v.toBCF.norm_coe_le_norm y)
        (schwartz_norm_le_of_mem_ball_gen ψ x₀ x y hx) (norm_nonneg _) (norm_nonneg _)
    · exact (((integrable_one_add_norm_sub_rpow x₀).const_mul _).const_mul _)
    · apply ae_of_all; intro y
      exact continuousAt_const.smul
        (ψ.continuous.continuousAt.comp (continuousAt_id.sub continuousAt_const))
  | succ k ih =>
    simp only [Nat.cast_succ]
    rw [contDiff_succ_iff_hasFDerivAt]
    exact ⟨fun x₀ => ∫ y, v y • (SchwartzMap.fderivCLM ℝ _ F ψ : _ → _) (x₀ - y) ∂volume,
      ih (SchwartzMap.fderivCLM ℝ _ F ψ),
      fun x₀ => hasFDerivAt_smul_convolution_schwartz v ψ x₀⟩

end ConvolutionDensity

namespace ConvolutionDensity

/--
[contDiff_convolution_zeroAtInfty_schwartz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionSchwartzDeriv.lean)
-/
@[path]
lemma contDiff_convolution_zeroAtInfty_schwartz
  {n : ℕ}
  {v : C₀(EuclideanSpace ℝ (Fin n), ℂ)}
  {ψ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ} :
-- imply
  ContDiff ℝ ∞ (fun x => ∫ y, v y * ψ (x - y) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
-- proof
  exact contDiff_infty.mpr fun k => by
    have h := contDiff_smul_convolution_schwartz v ψ k
    convert h using 2

end ConvolutionDensity

namespace ConvolutionDensity

/--
[tendsto_convolution_zeroAtInfty_schwartz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionSchwartzDeriv.lean)
-/
@[path]
lemma tendsto_convolution_zeroAtInfty_schwartz
  {n : ℕ}
  {n : ℕ}
  {v : C₀(EuclideanSpace ℝ (Fin n), ℂ)}
  {ψ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ} :
-- imply
  Tendsto (fun x => ∫ y, v y * ψ (x - y) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) := by
-- proof
  have hsub : ∀ x : EuclideanSpace ℝ (Fin n),
    ∫ y, v y * ψ (x - y) ∂volume = ∫ z, v (x - z) * ψ z ∂volume := by
    intro x
    rw [← integral_sub_left_eq_self (fun z => v (x - z) * ψ z) volume x]
    congr 1; ext y; simp [sub_sub_cancel]
  simp_rw [hsub]
  rw [show (0 : ℂ) = ∫ z, (0 : ℂ) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) from by simp]
  apply tendsto_integral_filter_of_dominated_convergence (fun z => ‖v.toBCF‖ * ‖(ψ : _ → _) z‖)
  ·
    apply Eventually.of_forall; intro x
    exact (v.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul
      ψ.continuous.aestronglyMeasurable
  ·
    apply Eventually.of_forall; intro x
    apply ae_of_all; intro z
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (v.toBCF.norm_coe_le_norm _) (norm_nonneg _)
  ·
    exact ψ.integrable.norm.const_mul _
  ·
    apply ae_of_all; intro z
    have hv_tendsto : Tendsto (fun x => v (x - z)) (cocompact _) (𝓝 0) :=
      (zero_at_infty v).comp
        ((isProperMap_iff_tendsto_cocompact.mp (Homeomorph.subRight z).isProperMap).2)
    rw [show (0 : ℂ) = 0 * ψ z from by ring]
    exact hv_tendsto.mul tendsto_const_nhds

end ConvolutionDensity

namespace ConvolutionDensity

/--
[prop_8_1_smooth_zeroAtInfty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionSchwartzDeriv.lean)
-/
@[path]
lemma prop_8_1_smooth_zeroAtInfty
  {n : ℕ}
  {v : C₀(EuclideanSpace ℝ (Fin n), ℂ)}
  {ψ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ} :
-- imply
  ContDiff ℝ ∞ (fun x => ∫ y, v y * ψ (x - y) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧ Tendsto (fun x => ∫ y, v y * ψ (x - y) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) :=
-- proof
  ⟨contDiff_convolution_zeroAtInfty_schwartz v ψ,
    tendsto_convolution_zeroAtInfty_schwartz v ψ⟩

end ConvolutionDensity


-- created on 2026-10-23
