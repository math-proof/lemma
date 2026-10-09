import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.W0.eq.Sum_MulProbIntegral.of.All_LeNorm.StronglyMeasurable
import Lemma.Real.Norm.le.Sum_Norm
import Lemma.Real.StronglyMeasurable.discrete
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
`W θ (f ∘ s) 0 y = f y`: the `0`-step kernel expectation of a state function is the function itself.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (f : S → ℝ)
  (y : S) :
-- imply
  M.W θ (fun z => f z.2.1) 0 y = f y := by
-- proof
  have := M.env.reward_markov
  rw [W0.eq.Sum_MulProbIntegral.of.All_LeNorm.StronglyMeasurable (M := M) (f := fun z => f z.2.1) ((StronglyMeasurable.discrete f).comp_measurable measurable_snd.fst) (fun z => Norm.le.Sum_Norm f z.2.1) θ]
  simp [← Finset.sum_mul, M.pol.sum_eq_one]


-- created on 2026-10-07
