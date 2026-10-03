import Lemma.Measure.Count.eq.ProdCountS
import Lemma.Random.PSpace.of.Measure.eq.Count.Measurable
import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


/--
The joint law of two measurable discrete random variables has a density.
If `x : Ω → α` and `y : Ω → β` are measurable, `α` and `β` are countable (with measurable singletons)
and both reference measures are the counting measure, then the pair `(x, y)` spans a
`SinglePSpace π` with respect to the product reference measure.
-/
@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  [Countable α] [MeasurableSingletonClass α] [Countable β] [MeasurableSingletonClass β]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : Ω → α} {y : Ω → β}
-- given
  (hx : Measurable x)
  (hy : Measurable y)
  (hα : ReferenceMeasure.measure (α := α) = Measure.count)
  (hβ : ReferenceMeasure.measure (α := β) = Measure.count) :
-- imply
  SinglePSpace π (x, y) := by
-- proof
  apply Random.PSpace.of.Measure.eq.Count.Measurable (hx.prodMk hy)
  show (ReferenceMeasure.measure : Measure α).prod (ReferenceMeasure.measure : Measure β) = _
  rw [hα, hβ, Measure.Count.eq.ProdCountS]


-- created on 2026-10-03
