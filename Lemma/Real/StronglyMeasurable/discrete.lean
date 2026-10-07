import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
Every real function on a countable measurable space with measurable singletons is strongly measurable.
-/
@[main]
private lemma main
  [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
-- given
  (φ : α → ℝ) :
-- imply
  StronglyMeasurable φ := by
-- proof
  exact StronglyMeasurable.of_discrete


-- created on 2026-10-07
