module
public import Mathlib.SetTheory.Cardinal.Aleph
public import Instance.Analysis.MeasureTheory.Section_1_4_1.Part4
public import Theorem.Analysis.MeasureTheory.Section_1_4_2.Part4


public section

/-- Definition 1.4.16 (Borel σ-algebra) -/
def BorelSigmaAlgebra (X:Type*) [TopologicalSpace X] : ConcreteSigmaAlgebra X :=
  ConcreteSigmaAlgebra.generated_by { U : Set X | IsOpen U }

