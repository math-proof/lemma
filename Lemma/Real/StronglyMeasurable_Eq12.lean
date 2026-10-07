import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Real.StronglyMeasurable.discrete
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Real


/--
The state indicator `z ↦ 1{z.s = x}` is strongly measurable.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [DecidableEq S]
-- given
  (x : S) :
-- imply
  StronglyMeasurable (fun z : ℝ × S × A => if z.2.1 = x then (1:ℝ) else 0) := by
-- proof
  exact (StronglyMeasurable.discrete (fun y : S => if y = x then (1:ℝ) else 0)).comp_measurable measurable_snd.fst


-- created on 2026-10-07
