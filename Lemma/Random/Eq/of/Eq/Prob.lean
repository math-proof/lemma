import Mathlib.Probability.Independence.Integration
import sympy.stats.joint_rv
import sympy.stats.variance
import sympy.Basic
open MeasureTheory


@[main]
private lemma given
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω}
  {x : Ω → α}
  {y : Ω → α}
-- given
  [SinglePSpace π x]
  [SinglePSpace π y]
  (h : x = y) :
-- imply
  π.prob x = π.prob y := by
-- proof
  subst h
  rfl


-- created on 2023-03-23
