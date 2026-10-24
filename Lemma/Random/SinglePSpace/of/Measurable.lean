import Lemma.Random.SinglePSpace.of.AEMeasurable
open MeasureTheory Random


@[path]
private lemma main
  [MeasurableSpace Ω]
  [CountableMeasure α]
  [Countable α] [MeasurableSingletonClass α]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : Ω → α}
-- given
  (hx : Measurable x) :
-- imply
  SinglePSpace π x := by
-- proof
  apply SinglePSpace.of.AEMeasurable hx.aemeasurable


-- created on 2026-09-21
-- updated on 2026-10-23
