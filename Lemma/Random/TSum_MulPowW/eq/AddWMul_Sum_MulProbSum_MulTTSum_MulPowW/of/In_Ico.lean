import Lemma.Random.Summable_MulPowWRc.of.In_Ico
import Lemma.Random.WAdd_1.eq.Sum_MulProbSum_MulTW.of.All_LeNorm.StronglyMeasurable
import Lemma.Real.Summable_MulPowSum_Mul.of.All_Summable_MulPow
import Lemma.Real.TSum_MulPowSum_Mul.eq.Sum_Mul_TSum_MulPow.of.All_Summable_MulPow
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
Bellman equation of the time-free value series:
`∑' k, γ ^ k * ∫ z, Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z ∂(stageK θ x) = ∫ z, Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) 0 z ∂(stageK θ x) +
  γ * ∑ u, π_θ(u | x) * ∑ y, T(x, u, y) * ∑' k, γ ^ k * ∫ z, Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z ∂(stageK θ y)`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (hγ : γ ∈ Set.Ico 0 1)
  (θ : Θ)
  (x : S) :
-- imply
  ∑' k, γ ^ k * ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z ∂(M.stageK θ x) = ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) 0 z ∂(M.stageK θ x) +
    γ * ∑ u, M.policy.prob θ x u * ∑ y, (M.env.trans (x, u)).real {y} * ∑' k, γ ^ k * ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z ∂(M.stageK θ y) := by
-- proof
  rw [(Summable_MulPowWRc.of.In_Ico (M := M) hγ θ x).tsum_eq_zero_add, pow_zero, one_mul]
  congr 1
  simp_rw [WAdd_1.eq.Sum_MulProbSum_MulTW.of.All_LeNorm.StronglyMeasurable (M := M) (Random.StronglyMeasurableClip (M := M)) (NormClip.le.AbsR (M := M)) θ, pow_succ, mul_comm _ γ, mul_assoc γ]
  rw [tsum_mul_left, TSum_MulPowSum_Mul.eq.Sum_Mul_TSum_MulPow.of.All_Summable_MulPow _ (fun u => Summable_MulPowSum_Mul.of.All_Summable_MulPow _ (fun y => Summable_MulPowWRc.of.In_Ico (M := M) hγ θ y) _) _]
  congr 1
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [TSum_MulPowSum_Mul.eq.Sum_Mul_TSum_MulPow.of.All_Summable_MulPow _ (fun y => Summable_MulPowWRc.of.In_Ico (M := M) hγ θ y) _]


-- created on 2026-10-07
-- updated on 2026-10-12
