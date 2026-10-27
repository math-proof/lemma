import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Lemma.Measure.Count.eq.ProdCountS
import Class.Probability.Rv.Part2
open MeasureTheory


attribute [instance] ReferenceMeasure.toSigmaFinite

attribute [simp] CountableMeasure.measure_eq_count


/-- Matches the `ReferenceMeasure (Fin n → α)` instance above (counting measure).
Also provides that `ReferenceMeasure` via `extends`. Construct other instances by
filling the parent fields (or `toReferenceMeasure := …`) plus `measure_eq_count`. -/
noncomputable instance {n : ℕ} {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] :
    CountableMeasure (Fin n → α) where
  measure := (Measure.count : Measure (Fin n → α))
  toSigmaFinite := inferInstance
  measure_eq_count := rfl

/-- Product of counting reference measures is again counting (`ReferenceMeasure.prod`). -/
noncomputable instance instCountableMeasureProd
    [CountableMeasure α] [CountableMeasure β]
    [Countable α] [MeasurableSingletonClass α] [Countable β] [MeasurableSingletonClass β] :
    CountableMeasure (α × β) where
  measure_eq_count := by
    change (ReferenceMeasure.measure : Measure α).prod ReferenceMeasure.measure = Measure.count
    rw [CountableMeasure.measure_eq_count, CountableMeasure.measure_eq_count,
      Measure.Count.eq.ProdCountS]


