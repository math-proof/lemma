import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.NormRc.le.Abs_R
import Lemma.Random.StronglyMeasurableRc
import Lemma.Random.Summable_MulPowWRc.of.In_Ico
import Lemma.Random.WAdd_1.eq.Sum_MulProbSum_MulTW.of.All_LeNorm.StronglyMeasurable
import Lemma.Real.Summable_MulPowSum_Mul.of.All_Summable_MulPow
import Lemma.Real.TSum_MulPowSum_Mul.eq.Sum_Mul_TSum_MulPow.of.All_Summable_MulPow
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
Bellman equation of the time-free value series:
`∑' k, γ ^ k * W θ rc k x = W θ rc 0 x + γ * ∑ u, π_θ(u | x) * ∑ y, T(x, u, y) * ∑' k, γ ^ k * W θ rc k y`.
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
  ∑' k, γ ^ k * M.W θ M.rc k x = M.W θ M.rc 0 x +
    γ * ∑ u, M.pol.prob θ x u * ∑ y, M.T x u y * ∑' k, γ ^ k * M.W θ M.rc k y := by
-- proof
  rw [(Summable_MulPowWRc.of.In_Ico (M := M) hγ θ x).tsum_eq_zero_add, pow_zero, one_mul]
  congr 1
  simp_rw [WAdd_1.eq.Sum_MulProbSum_MulTW.of.All_LeNorm.StronglyMeasurable (M := M) (Random.StronglyMeasurableRc (M := M)) (NormRc.le.Abs_R (M := M)) θ, pow_succ, mul_comm _ γ, mul_assoc γ]
  rw [tsum_mul_left, TSum_MulPowSum_Mul.eq.Sum_Mul_TSum_MulPow.of.All_Summable_MulPow _ (fun u => Summable_MulPowSum_Mul.of.All_Summable_MulPow _ (fun y => Summable_MulPowWRc.of.In_Ico (M := M) hγ θ y) _) _]
  congr 1
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [TSum_MulPowSum_Mul.eq.Sum_Mul_TSum_MulPow.of.All_Summable_MulPow _ (fun y => Summable_MulPowWRc.of.In_Ico (M := M) hγ θ y) _]


-- created on 2026-10-07
