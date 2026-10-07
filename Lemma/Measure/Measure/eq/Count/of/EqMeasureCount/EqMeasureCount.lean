import Lemma.Measure.Count.eq.ProdCountS
import sympy.stats.rv
import sympy.Basic
open MeasureTheory


/--
The reference measure of a product of two discrete state spaces is the counting measure.
If `α` and `β` are countable (with measurable singletons) and both reference measures are the
counting measure, then so is the product reference measure on `α × β`, i.e. the product of
the two counting measures is the counting measure.
-/
@[main]
private lemma main
  [ReferenceMeasure α] [ReferenceMeasure β]
  [Countable α] [MeasurableSingletonClass α] [Countable β] [MeasurableSingletonClass β]
-- given
  (hα : ReferenceMeasure.measure (α := α) = Measure.count)
  (hβ : ReferenceMeasure.measure (α := β) = Measure.count) :
-- imply
  ReferenceMeasure.measure (α := α × β) = Measure.count := by
-- proof
  show (ReferenceMeasure.measure : Measure α).prod (ReferenceMeasure.measure : Measure β) = _
  rw [hα, hβ, Measure.Count.eq.ProdCountS]


-- created on 2026-10-04
