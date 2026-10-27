import Lemma.Random.SinglePSpace.of.Measurable
import Lemma.Random.SinglePSpace.of.Measurable.Measurable
open MeasureTheory Random


/-- From `Fact (Measurable x)`, infer `SinglePSpace π x`. -/
instance {Ω α : Type*} [MeasurableSpace Ω]
    [CountableMeasure α] [Countable α] [MeasurableSingletonClass α]
    {π : Measure Ω} [IsProbabilityMeasure π]
    {x : Ω → α} [hx : Fact (Measurable x)] :
    SinglePSpace π x :=
  SinglePSpace.of.Measurable hx.out

/--
From `Fact (Measurable x)` and `Fact (Measurable y)`, infer a joint `SinglePSpace π (x, y)`
via `SinglePSpace.of.Measurable.Measurable`. Prefer `[Fact (Measurable …)]` binders when the
goal is to drop an explicit `hslice : SinglePSpace …` argument; plain `(hx : Measurable …)`
cannot feed typeclass search because `Measurable` is not a class.
-/
instance {Ω α β : Type*} [MeasurableSpace Ω]
    [CountableMeasure α] [CountableMeasure β]
    [Countable α] [MeasurableSingletonClass α]
    [Countable β] [MeasurableSingletonClass β]
    {π : Measure Ω} [IsProbabilityMeasure π]
    {x : Ω → α} {y : Ω → β}
    [hx : Fact (Measurable x)] [hy : Fact (Measurable y)] :
    SinglePSpace π (x, y) :=
  SinglePSpace.of.Measurable.Measurable hx.out hy.out

