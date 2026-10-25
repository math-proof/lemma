import Mathlib.SetTheory.Cardinal.Aleph
import Instance.Analysis.MeasureTheory.Section_1_4_1.Part4
import Theorem.Analysis.MeasureTheory.Section_1_4_2.Part3


def ConcreteSigmaAlgebra.restrict {X:Type*} (B: ConcreteSigmaAlgebra X) (A:Set X) : ConcreteSigmaAlgebra A := (B.restrict_is_sigma A).toSigmaAlgebra

