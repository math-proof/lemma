import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Real.StronglyMeasurable.discrete
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Real


/--
The action indicator `z ↦ 1{z.a = u}` is strongly measurable.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq A]
-- given
  (u : A) :
-- imply
  StronglyMeasurable (fun z : ℝ × S × A => if z.2.2 = u then (1:ℝ) else 0) := by
-- proof
  exact (StronglyMeasurable.discrete (fun v : A => if v = u then (1:ℝ) else 0)).comp_measurable measurable_snd.snd


-- created on 2026-10-07
