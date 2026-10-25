import Def.Analysis.MeasureTheory.Section_1_4_2.Part8
import Theorem.Analysis.MeasureTheory.Section_1_4_3.Part3


def FinitelyAdditiveMeasure.isCountablyAdditive {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) : Prop :=
  B.isSigmaAlgebra ∧ ∀ (E : ℕ → Set X), (∀ n, B.measurable (E n)) → Set.univ.PairwiseDisjoint E →
    μ.measure (⋃ n, E n) = ∑' n, (μ.measure (E n))

def FinitelyAdditiveMeasure.isCountablyAdditive.toCountablyAdditive {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) (h: μ.isCountablyAdditive) : CountablyAdditiveMeasure h.1.toSigmaAlgebra :=
  {
    measure := μ.measure
    measure_pos := μ.measure_pos
    measure_empty := μ.measure_empty
    measure_finite_additive := μ.measure_finite_additive
    measure_countable_additive := h.2
  }

