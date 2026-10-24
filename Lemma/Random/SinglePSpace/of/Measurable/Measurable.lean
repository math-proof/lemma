import Lemma.Random.SinglePSpace.of.Measurable
import sympy.stats.joint_rv
open MeasureTheory Random


/--
The joint law of two measurable discrete random variables has a density.
If `x : Ω → α` and `y : Ω → β` are measurable and `α`, `β` carry the counting measure
(`[CountableMeasure α]` / `[CountableMeasure β]`, countable, with measurable singletons),
then the pair `(x, y)` spans a `SinglePSpace π` with respect to the product reference measure.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [CountableMeasure α] [CountableMeasure β]
  [Countable α] [MeasurableSingletonClass α] [Countable β] [MeasurableSingletonClass β]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : Ω → α} {y : Ω → β}
-- given
  (hx : Measurable x)
  (hy : Measurable y) :
-- imply
  SinglePSpace π (x, y) := by
-- proof
  apply SinglePSpace.of.Measurable (hx.prodMk hy)

-- created on 2026-10-22
-- updated on 2026-10-23
