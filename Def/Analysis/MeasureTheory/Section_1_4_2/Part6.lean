import Mathlib.SetTheory.Cardinal.Aleph
import Instance.Analysis.MeasureTheory.Section_1_4_1.Part4
import Theorem.Analysis.MeasureTheory.Section_1_4_2.Part4


/-- Definition 1.4.16 (Borel σ-algebra) -/
def BorelSigmaAlgebra (X:Type*) [TopologicalSpace X] : ConcreteSigmaAlgebra X :=
  ConcreteSigmaAlgebra.generated_by { U : Set X | IsOpen U }

