import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Real.StronglyMeasurable.discrete
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Real


/--
Every real function of a measurable finite-valued random variable is integrable: `Integrable (φ ∘ X)`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A] [MeasurableSpace B] [MeasurableSingletonClass B] [Fintype B]
  {M : Model Θ S A}
-- given
  (X : (ℕ → ℝ × S × A) → B)
  (hX : Measurable X)
  (θ : Θ)
  (φ : B → ℝ) :
-- imply
  Integrable (fun ω => φ (X ω)) (M θ) := by
-- proof
  refine Integrable.of_bound (C := ∑ b, ‖φ b‖) ((StronglyMeasurable.discrete φ).comp_measurable hX).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  exact Finset.single_le_sum (f := fun b => ‖φ b‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ _)


-- created on 2026-10-07
