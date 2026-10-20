import Lemma.Random.Integral.eq.Sum_MulRealEq
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
  M.Vc θ γ x = ∑ u, M.policy.prob θ x u * M.Qc θ γ x u := by
-- proof
  rw [Vc.eq.TSum_MulPowIntegral.of.In_Ico (M := M) h₀ θ x,
    TSum_MulPowW.eq.AddWMul_Sum_MulProbSum_MulTTSum_MulPowW.of.In_Ico (M := M) h₀ θ x]
  simp_rw [← Vc.eq.TSum_MulPowIntegral.of.In_Ico (M := M) h₀]
  have hKf0 : M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) 0 =
      fun z ↦ clip z.1 (-M.env.R) M.env.R := rfl
  simp_rw [hKf0]
  unfold Model.Qc
  simp only [Expectation.ofRV, expectation_real, Expectation.asRV_function, Measure.map_id]
  have := M.env.trans_markov
  have hE : ∀ u, ∫ y, M.Vc θ γ y ∂(M.env.trans (x, u)) =
      ∑ y, (M.env.trans (x, u)).real {y} * M.Vc θ γ y := fun u => by
    have : IsProbabilityMeasure (M.env.trans (x, u)) := inferInstance
    simpa using Integral.eq.Sum_MulRealEq (μ := M.env.trans (x, u)) (L := (id : S → S)) (M.Vc θ γ)
  simp_rw [hE]
  rw [W0.eq.Sum_MulProbIntegral.of.All_LeNorm.StronglyMeasurable (M := M)
    (Random.StronglyMeasurableClip (M := M)) (NormClip.le.AbsR (M := M)) θ x]
  -- LHS: ∑ u, π * ∫clip + γ * ∑ u, π * ∑ y, T * Vc
  -- RHS: ∑ u, π * (∫clip + γ * ∑ y, T * Vc)
  conv_lhs => enter [2]; rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  ring


-- created on 2026-10-06
-- updated on 2026-10-20
