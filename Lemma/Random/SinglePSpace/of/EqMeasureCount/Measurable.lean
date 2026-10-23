import Lemma.Random.SinglePSpace.of.EqMeasureCount.AEMeasurable
open MeasureTheory Random


@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  [Countable α] [MeasurableSingletonClass α]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : Ω → α}
-- given
  (hx : Measurable x)
  (hμ : ReferenceMeasure.measure (α := α) = Measure.count) :
-- imply
  SinglePSpace π x := by
-- proof
  apply SinglePSpace.of.EqMeasureCount.AEMeasurable hx.aemeasurable hμ


-- created on 2026-09-21
-- updated on 2026-10-23
