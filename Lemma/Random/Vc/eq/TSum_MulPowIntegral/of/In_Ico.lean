import sympy.stats.policy_trajectory.gradient
import Lemma.Random.StronglyMeasurableClip
import Lemma.Random.NormClip.le.AbsR
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
`Vc θ γ y = ∑' k, γ ^ k * ∫ z, Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z ∂(stageK θ y)`.
(New `Vc` is Expectation of Dot; interchange integral/tsum via clipped bound and geometric series.)
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (θ : Θ)
  (y : S) :
-- imply
  M.Vc θ γ y = ∑' k, γ ^ k * ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z ∂(M.stageK θ y) := by
-- proof
  unfold Model.Vc
  simp only [Expectation.ofRV, expectation_real, Expectation.asRV_function, Measure.map_id]
  -- ∫ z, (γ ^ id) @ (fun j ↦ Kf j z) ∂(stageK θ y)
  change ∫ z, (γ ^ (id : ℕ → ℕ)) @ (fun j ↦ M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) j z)
      ∂(M.stageK θ y) =
    ∑' k, γ ^ k * ∫ z, M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) k z ∂(M.stageK θ y)
  dsimp only [Dot.dot]
  simp only [Function.hPow_apply, id_eq]
  -- ∫ ∑' k, γ ^ k * Kf k z  =  ∑' k, γ ^ k * ∫ Kf k z
  have hK : ∀ k, StronglyMeasurable (M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) k) ∧
      ∀ z, ‖M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) k z‖ ≤ |M.env.R| :=
    fun k => StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable (M := M)
      (Random.StronglyMeasurableClip (M := M)) (NormClip.le.AbsR (M := M)) θ k
  have hF : ∀ k, Integrable (fun z => γ ^ k * M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) k z)
      (M.stageK θ y) := fun k =>
    Integrable.of_bound ((hK k).1.const_mul (γ ^ k)).aestronglyMeasurable (γ ^ k * |M.env.R|)
      (Filter.Eventually.of_forall fun z => by
        rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
        exact mul_le_mul_of_nonneg_left ((hK k).2 z) (pow_nonneg h₀.1 k))
  have hS : Summable (fun k => ∫ z, ‖γ ^ k * M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) k z‖
      ∂(M.stageK θ y)) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun z => norm_nonneg _) (fun k => ?_)
      ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|)
    have hb : ∀ᵐ z ∂(M.stageK θ y),
        ‖‖γ ^ k * M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) k z‖‖ ≤ γ ^ k * |M.env.R| :=
      Filter.Eventually.of_forall fun z => by
        rw [norm_norm, norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
        exact mul_le_mul_of_nonneg_left ((hK k).2 z) (pow_nonneg h₀.1 k)
    have := norm_integral_le_of_norm_le_const hb
    simp only [probReal_univ, mul_one] at this
    exact (Real.le_norm_self _).trans this
  rw [← (hasSum_integral_of_summable_integral_norm hF hS).tsum_eq]
  exact tsum_congr fun k => integral_const_mul _ _


-- created on 2026-10-11
-- updated on 2026-10-20
