module

public import Theorem.Random.SinglePSpace.of.AEMeasurable

public section

open MeasureTheory Random


public theorem Random.SinglePSpace.of.Measurable
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
