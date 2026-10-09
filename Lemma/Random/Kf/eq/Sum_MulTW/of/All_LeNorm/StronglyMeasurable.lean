import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.Integral.eq.Integral_Integral.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
One more step of the iterated kernel expectation: `Kf θ f (j+1) z = ∑ y, T(z.s, z.a, y) * W θ f j y`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {f : ℝ × S × A → ℝ}
  {C : ℝ}
-- given
  (hf : StronglyMeasurable f)
  (hC : ∀ z, ‖f z‖ ≤ C)
  (θ : Θ)
  (j : ℕ)
  (z : ℝ × S × A) :
-- imply
  M.Kf θ f (j + 1) z = ∑ y, M.T z.2.1 z.2.2 y * M.W θ f j y := by
-- proof
  have := M.env.trans_markov
  show ∫ w, M.Kf θ f j w ∂(M.K θ z) = _
  have hK : M.K θ z = M.stageK θ ∘ₘ M.env.trans (z.2.1, z.2.2) := by
    rw [Model.K, Kernel.comp_apply, Kernel.comap_apply]
  rw [hK, Integral.eq.Integral_Integral.of.All_LeNorm.StronglyMeasurable (StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable (M := M) hf hC θ j).1 (StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable (M := M) hf hC θ j).2,
    integral_fintype Integrable.of_finite]
  rfl


-- created on 2026-10-07
