import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Real.StronglyMeasurable.discrete
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Real


/--
The state-action indicator `z ↦ 1{z.s = x ∧ z.a = u}` is strongly measurable.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
-- given
  (x : S)
  (u : A) :
-- imply
  StronglyMeasurable (fun z : ℝ × S × A => if z.2.1 = x ∧ z.2.2 = u then (1:ℝ) else 0) := by
-- proof
  exact (StronglyMeasurable.discrete (fun p : S × A => if p.1 = x ∧ p.2 = u then (1:ℝ) else 0)).comp_measurable
    (measurable_snd.fst.prodMk measurable_snd.snd)


-- created on 2026-10-07
