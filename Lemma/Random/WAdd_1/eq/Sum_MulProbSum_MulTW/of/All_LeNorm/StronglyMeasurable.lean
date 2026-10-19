import Lemma.Random.Integral.eq.Sum_SMul.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.Kf.eq.Sum_MulTW.of.All_LeNorm.StronglyMeasurable
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
Recursion of the time-homogeneous kernel expectation:
`∫ z, Kf θ f (j+1) z ∂(stageK θ x) = ∑ u, π_θ(u | x) * ∑ y, T(x, u, y) * ∫ z, Kf θ f j z ∂(stageK θ y)`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {f : ℝ × S × A → ℝ}
  {C : ℝ}
-- given
  (hf : StronglyMeasurable f)
  (hC : ∀ z, ‖f z‖ ≤ C)
  (θ : Θ)
  (j : ℕ)
  (x : S) :
-- imply
  ∫ z, M.Kf θ f (j + 1) z ∂(M.stageK θ x) =
    ∑ u, M.policy.prob θ x u * ∑ y, (M.env.trans (x, u)).real {y} * ∫ z, M.Kf θ f j z ∂(M.stageK θ y) := by
-- proof
  have := M.env.reward_markov
  have h := StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable (M := M) hf hC θ (j + 1)
  rw [Integral.eq.Sum_SMul.of.All_LeNorm.StronglyMeasurable (M := M) h.1 h.2 θ]
  simp_rw [Kf.eq.Sum_MulTW.of.All_LeNorm.StronglyMeasurable (M := M) hf hC θ j]
  simp [smul_eq_mul]


-- created on 2026-10-07
