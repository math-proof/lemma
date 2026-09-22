import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import sympy.stats.rv
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  [Countable α] [MeasurableSingletonClass α]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : Ω → α}
-- given
  (hx : Measurable x)
  (hμ : ReferenceMeasure.measure (α := α) = Measure.count) :
-- imply
  PSpace π x := by
-- proof
  have hx_m : AEMeasurable x π := hx.aemeasurable
  have hacc : π.map x ≪ ReferenceMeasure.measure := by
    rw [hμ]
    intro s hs0
    have hs_empty : s = (∅ : Set α) := Measure.count_eq_zero_iff.mp hs0
    rw [hs_empty]
    exact measure_empty
  let q : α → ENNReal := (π.map x).rnDeriv ReferenceMeasure.measure
  have hq : Measurable q := Measure.measurable_rnDeriv _ _
  have hlaw : π.map x = ReferenceMeasure.measure.withDensity q :=
    (Measure.withDensity_rnDeriv_eq _ _ hacc).symm
  exact { toIsProbabilityMeasure := inferInstance
          aemeasurable := hx_m
          exists_distribution := ⟨q, ⟨hq⟩, hlaw⟩ }


-- created on 2026-09-21
