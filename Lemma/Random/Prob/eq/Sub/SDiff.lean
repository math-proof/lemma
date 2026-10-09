import Mathlib.Probability.Independence.Integration
import sympy.stats.joint_rv
import sympy.stats.variance
import sympy.Basic
open MeasureTheory


@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω}
  {x : Ω → α}
  {s : Set α}
-- given
  [SinglePSpace π x]
  (hs : MeasurableSet s) :
-- imply
  Probability π x s = 1 - Probability π x sᶜ := by
-- proof
  unfold Probability
  have hP : PSpace π x := ‹SinglePSpace π x›.toPSpace
  have : IsProbabilityMeasure π := hP.toIsProbabilityMeasure
  have : IsProbabilityMeasure (π.map x) := inferInstance
  rw [prob_compl_eq_one_sub hs, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]


-- created on 2023-04-19
