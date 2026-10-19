import Lemma.Random.Integral.eq.Sum_SMul.of.All_LeNorm.StronglyMeasurable
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
`∫ z, f z ∂(stageK θ x) = ∑ u, π_θ(u | x) * ∫ ρ, f (ρ, x, u) ∂(reward (x, u))`.
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
  (x : S) :
-- imply
  ∫ z, f z ∂(M.stageK θ x) = ∑ u, M.policy.prob θ x u * ∫ ρ, f (ρ, x, u) ∂(M.env.reward (x, u)) := by
-- proof
  rw [Integral.eq.Sum_SMul.of.All_LeNorm.StronglyMeasurable (M := M) hf hC θ x]
  simp [smul_eq_mul]


-- created on 2026-10-07
