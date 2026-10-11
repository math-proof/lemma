import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.NormRc.le.AbsR
import Lemma.Random.StronglyMeasurableRc
import Lemma.Random.TSum_MulPowW.eq.AddWMul_Sum_MulProbSum_MulTTSum_MulPowW.of.In_Ico
import Lemma.Random.Vc.eq.TSum_MulPowIntegral.of.In_Ico
import Lemma.Random.W0.eq.Sum_MulProbIntegral.of.All_LeNorm.StronglyMeasurable
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
Bellman equation of the time-free closed-form values: `Vc θ γ x = ∑ u, π_θ(u | x) * Qc θ γ x u`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (θ : Θ)
  (x : S) :
-- imply
  M.Vc θ γ x = ∑ u, M.pol.prob θ x u * M.Qc θ γ x u := by
-- proof
  rw [Vc.eq.TSum_MulPowIntegral.of.In_Ico (M := M) θ x]
  unfold Model.Qc
  simp_rw [Vc.eq.TSum_MulPowIntegral.of.In_Ico (M := M)]
  rw [TSum_MulPowW.eq.AddWMul_Sum_MulProbSum_MulTTSum_MulPowW.of.In_Ico (M := M) h₀ θ x]
  change ∫ z, clip z.1 (-M.env.R) M.env.R ∂(M.stageK θ x) + _ =
    ∑ u, M.pol.prob θ x u * (∫ ρ, clip ρ (-M.env.R) M.env.R ∂(M.env.reward (x, u)) + _)
  rw [W0.eq.Sum_MulProbIntegral.of.All_LeNorm.StronglyMeasurable (M := M)
    (Random.StronglyMeasurableRc (M := M)) (NormRc.le.AbsR (M := M)) θ x, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  ring


-- created on 2026-10-06
-- updated on 2026-10-11
