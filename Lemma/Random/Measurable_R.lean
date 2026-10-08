import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory Topology PolicyGradient


/--
The reward coordinate `r[k]` of the trajectory is measurable.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSpace A]
-- given
  (k : ℕ) :
-- imply
  Measurable (reward (S := S) (A := A) k) :=
-- proof
  measurable_fst.comp (measurable_pi_apply k)


-- created on 2026-10-06
