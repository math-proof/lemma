import Mathlib.SetTheory.Cardinal.Aleph
import Instance.Analysis.MeasureTheory.Section_1_4_1.Part4
import Instance.Analysis.MeasureTheory.Section_1_4_2


def ConcreteSigmaAlgebra.generated_by {X:Type*} (F: Set (Set X)) : ConcreteSigmaAlgebra X :=
  sInf { B | ∀ E ∈ F, B.measurable E }

