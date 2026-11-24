module
public import Mathlib.SetTheory.Cardinal.Aleph
public import Instance.Analysis.MeasureTheory.Section_1_4_1.Part4
public import Instance.Analysis.MeasureTheory.Section_1_4_2


public section

def ConcreteSigmaAlgebra.generated_by {X:Type*} (F: Set (Set X)) : ConcreteSigmaAlgebra X :=
  sInf { B | ∀ E ∈ F, B.measurable E }

