import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.Integral.eq.Sum_SMul.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.Kf.eq.Sum_MulTW.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
Recursion of the time-homogeneous kernel expectation: `W θ f (j+1) x = ∑ u, π_θ(u | x) * ∑ y, T(x, u, y) * W θ f j y`.
-/
@[main]
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
  M.W θ f (j + 1) x = ∑ u, M.pol.prob θ x u * ∑ y, M.T x u y * M.W θ f j y := by
-- proof
  have := M.env.reward_markov
  have h := StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable (M := M) hf hC θ (j + 1)
  unfold Model.W
  rw [Integral.eq.Sum_SMul.of.All_LeNorm.StronglyMeasurable (M := M) h.1 h.2 θ]
  simp_rw [Kf.eq.Sum_MulTW.of.All_LeNorm.StronglyMeasurable (M := M) hf hC θ j]
  simp [smul_eq_mul]
  rfl


-- created on 2026-10-07
