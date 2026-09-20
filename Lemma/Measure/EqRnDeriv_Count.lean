import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Lemma.Measure.Ll_Count
open MeasureTheory Measure


@[main]
private lemma main
  [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  {μ : Measure α}
-- given
  (a : α) :
-- imply
  μ.rnDeriv count a = μ {a} := by
-- proof
  have hμ : μ ≪ (count : Measure α) := Ll_Count μ
  have h : (count : Measure α).withDensity (μ.rnDeriv count) = μ :=
    Measure.withDensity_rnDeriv_eq μ count hμ
  calc
    _ = μ.rnDeriv count a * (count : Measure α) {a} := by
      rw [count_singleton, mul_one]
    _ = ∫⁻ x in {a}, μ.rnDeriv count x ∂(count : Measure α) := by
      rw [lintegral_singleton]
    _ = ((count : Measure α).withDensity (μ.rnDeriv count)) {a} := by
      rw [withDensity_apply _ (measurableSet_singleton a)]
    _ = μ {a} := by
      rw [h]


-- created on 2026-09-20
