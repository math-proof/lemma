import sympy.stats.policy_trajectory.gradient
import sympy.Basic
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model


/--
The reward coordinate `r[k]` of the trajectory is measurable.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSpace A]
-- given
  (k : ℕ) :
-- imply
  Measurable (r (S := S) (A := A) k) := by
-- proof
  exact measurable_fst.comp (measurable_pi_apply k)


-- created on 2026-10-06
