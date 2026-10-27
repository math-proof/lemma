import Syntax.Probability.JointRv.Part6
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : MeasureTheory.Measure Ω} {x : Ω → α} [SinglePSpace π x]
-- given
  (ω : Ω) :
-- imply
  ℙ[π](x) ω = ℙ[π](x = x ω) := by
-- proof
  rfl


-- created on 2026-09-20
