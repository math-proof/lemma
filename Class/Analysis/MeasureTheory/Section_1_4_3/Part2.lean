import Def.Analysis.MeasureTheory.Section_1_4_2.Part8
import Theorem.Analysis.MeasureTheory.Section_1_4_3.Part2


/-- Definition 1.4.27 (Countably additive measure) -/
class CountablyAdditiveMeasure {X:Type*} (B: ConcreteSigmaAlgebra X) extends FinitelyAdditiveMeasure B.toConcreteBooleanAlgebra where
  measure_countable_additive : ∀ (E : ℕ → Set X), (∀ n, B.measurable (E n)) → Set.univ.PairwiseDisjoint E →
    measure (⋃ n, E n) = ∑' n, (measure (E n))

