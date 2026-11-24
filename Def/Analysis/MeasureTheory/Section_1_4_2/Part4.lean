module
public import Mathlib.SetTheory.Cardinal.Aleph
public import Instance.Analysis.MeasureTheory.Section_1_4_1.Part4
public import Theorem.Analysis.MeasureTheory.Section_1_4_2.Part3


public section

def ConcreteSigmaAlgebra.restrict {X:Type*} (B: ConcreteSigmaAlgebra X) (A:Set X) : ConcreteSigmaAlgebra A := (B.restrict_is_sigma A).toSigmaAlgebra

