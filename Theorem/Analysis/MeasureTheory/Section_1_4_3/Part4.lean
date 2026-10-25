import Def.Analysis.MeasureTheory.Section_1_4_2.Part8
import Def.Analysis.MeasureTheory.Section_1_4_3.Part3


/-- Example 1.4.28 -/
theorem FinitelyAdditiveMeasure.lebesgue_isCountablyAdditive (d:ℕ) : (FinitelyAdditiveMeasure.lebesgue d).isCountablyAdditive :=
  ⟨LebesgueMeasurable.boolean_algebra.isSigmaAlgebra d,
    fun _ hE hdisj => Lebesgue_measure.countable_union hE hdisj⟩

theorem FinitelyAdditiveMeasure.isCountablyAdditive_restrict_alg {X:Type*} {B B': ConcreteSigmaAlgebra X} (μ: CountablyAdditiveMeasure B) (hBB': B' ≤ B) : (μ.toFinitelyAdditiveMeasure.restrict_alg hBB').isCountablyAdditive :=
  ⟨B'.countable_union_mem, fun E hE hdisj =>
    μ.measure_countable_additive E (fun n => hBB' (E n) (hE n)) hdisj⟩

