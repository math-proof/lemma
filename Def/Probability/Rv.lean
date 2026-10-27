import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Lemma.Measure.Count.eq.ProdCountS
import Class.Probability.Rv
open MeasureTheory


attribute [instance] ReferenceMeasure.toSigmaFinite


/-- Build a `ReferenceMeasure` from an explicit σ-finite measure. -/
@[instance_reducible]
def ReferenceMeasure.of {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] : ReferenceMeasure α where
  toMeasurableSpace := inferInstance
  measure := μ
  toSigmaFinite := inferInstance

