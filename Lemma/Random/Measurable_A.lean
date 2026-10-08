import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
The action process `a t` of the trajectory space is measurable.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSpace A]
-- given
  (t : ℕ) :
-- imply
  Measurable (action (S := S) (A := A) t) := by
-- proof
  exact measurable_snd.snd.comp (measurable_pi_apply t)


-- created on 2026-10-07
