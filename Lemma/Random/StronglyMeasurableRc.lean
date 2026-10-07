import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
The clamped reward `rc` is strongly measurable.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A} :
-- imply
  StronglyMeasurable M.rc := by
-- proof
  exact (Measurable.max measurable_const (Measurable.min measurable_const measurable_fst)).stronglyMeasurable


-- created on 2026-10-07
