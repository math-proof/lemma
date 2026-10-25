import Def.Analysis.MeasureTheory.Section_1_4_2.Part8
import Instance.Analysis.MeasureTheory.Section_1_4_3.Part2
open MeasureTheory


noncomputable def FinitelyAdditiveMeasure.isCountablyAdditive.toMeasure {X:Type*} {B: ConcreteBooleanAlgebra X} {μ: FinitelyAdditiveMeasure B} (h: μ.isCountablyAdditive) :
  @Measure X h.1.toSigmaAlgebra.measurableSpace := h.toCountablyAdditive.toMeasure

noncomputable def EuclideanSpace'.lebesgueMeasure (d:ℕ) := (FinitelyAdditiveMeasure.lebesgue_isCountablyAdditive d).toMeasure

noncomputable def EuclideanSpace'.borelMeasure (d:ℕ) := ((FinitelyAdditiveMeasure.lebesgue_isCountablyAdditive d).toCountablyAdditive.restrict_alg (BorelSigmaAlgebra.le_LebesgueSigmaAlgebra d)).toMeasure

def Measure.equiv {X:Type*} {M M' : MeasurableSpace X} (μ: @Measure X M) (μ': @Measure X M') : Prop := M = M' ∧ ∀ E, M.MeasurableSet' E → μ E = μ' E

