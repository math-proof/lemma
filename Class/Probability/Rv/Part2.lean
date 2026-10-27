import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Lemma.Measure.Count.eq.ProdCountS
import Instance.Probability.Rv
open MeasureTheory


attribute [instance] ReferenceMeasure.toSigmaFinite


/--
The ambient `ReferenceMeasure` on `α` is the counting measure.

Extends `ReferenceMeasure`, so `[CountableMeasure α]` also provides `[ReferenceMeasure α]`
(and thus `[MeasurableSpace α]`). Use this instead of repeating
`(h : (ReferenceMeasure.measure : Measure α) = Measure.count)` on every lemma.
Typical GradExpect / discrete-HMM binders become
`[CountableMeasure S] [CountableMeasure A]` — no separate `ReferenceMeasure` binder.

Do **not** invent a global instance for every `[Countable α]`: the reference measure is a
chosen ambient, and may be Lebesgue (or other) even on a countable type. Provide
`[CountableMeasure α]` at the lemma / model boundary, or build from an existing
`ReferenceMeasure` with `measure_eq_count := h` when `h : measure = Measure.count`
(e.g. after `ReferenceMeasure.of Measure.count`).
-/
class CountableMeasure (α : Type*) extends ReferenceMeasure α where
  /-- The chosen reference measure equals `Measure.count`. -/
  measure_eq_count : measure = Measure.count

