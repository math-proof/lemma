import Mathlib.Probability.Independence.Integration
import Def.Probability.Moments.Variance
import Initialize.Tactic.Attr.Basic
open MeasureTheory


@[path]
private lemma main
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


-- created on 2020-12-13
