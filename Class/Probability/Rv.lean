import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Lemma.Measure.Count.eq.ProdCountS
open MeasureTheory


/--
Canonical state measure on a measurable space (e.g. Lebesgue on `ℝ`).

Extends `MeasurableSpace`, so `[ReferenceMeasure α]` also provides `[MeasurableSpace α]`.

This is the ambient measure that densities are taken with respect to — analogous to
how sympy treats continuous spaces without naming the measure explicitly.
Unlike a bare `∃ μ, SigmaFinite μ`, this **chooses** a specific measure.
-/
class ReferenceMeasure (α : Type*) extends MeasurableSpace α where
  /-- The state measure. -/
  measure : Measure α
  /-- State measures are required to be σ-finite (so Radon–Nikodym applies). -/
  toSigmaFinite : SigmaFinite measure

