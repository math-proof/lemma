import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import sympy.stats.rv
open MeasureTheory


/--
An almost-everywhere measurable random variable whose reference measure is counting
measure admits a density. `π.map x ≪ Measure.count`, so the Radon–Nikodym derivative
of that law is a distribution of `x`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [CountableMeasure α]
  [Countable α] [MeasurableSingletonClass α]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : Ω → α}
-- given
  (hx : AEMeasurable x π) :
-- imply
  SinglePSpace π x := by
-- proof
  have hacc : π.map x ≪ ReferenceMeasure.measure := by
    rw [CountableMeasure.measure_eq_count]
    intro s hs0
    rw [Measure.count_eq_zero_iff.mp hs0]
    apply measure_empty
  let q : α → ENNReal := (π.map x).rnDeriv ReferenceMeasure.measure
  exact {
    toIsProbabilityMeasure := inferInstance
    aemeasurable := hx
    exists_distribution := ⟨q, ⟨Measure.measurable_rnDeriv _ _⟩,
      (Measure.withDensity_rnDeriv_eq _ _ hacc).symm⟩
  }


-- created on 2026-10-23
-- updated on 2026-10-23
