import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.AeHasSumAndNormG.le.MulSub1Abs_R.of.In_Ico
import Lemma.Random.Measurable_R
open MeasureTheory ProbabilityTheory Finset Filter Topology PolicyGradient PolicyGradient.Model


/--
The discounted return `G[t]` is integrable under the trajectory model.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (θ : Θ)
  (h₀ : γ ∈ Set.Ico 0 1)
  (t : ℕ) :
-- imply
  Integrable (G γ t) (M θ) := by
-- proof
  have hm : AEStronglyMeasurable (G γ t) (M θ) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n ω => ∑ k ∈ Finset.range n, γ ^ k * r (t + k) ω) (fun n => ?_) ?_
    · exact (Finset.measurable_fun_sum _ fun k _ =>
        (Random.Measurable_R (t + k)).const_mul (γ ^ k)).aestronglyMeasurable
    · exact (Random.AeHasSumAndNormG.le.MulSub1Abs_R.of.In_Ico (M := M) θ h₀ t).mono fun ω h => h.1.tendsto_sum_nat
  exact Integrable.of_bound hm _ ((Random.AeHasSumAndNormG.le.MulSub1Abs_R.of.In_Ico (M := M) θ h₀ t).mono fun ω h => h.2)


-- created on 2026-10-06
