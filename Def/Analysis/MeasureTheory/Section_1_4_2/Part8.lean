import Mathlib.SetTheory.Cardinal.Aleph
import Instance.Analysis.MeasureTheory.Section_1_4_1.Part4
import Theorem.Analysis.MeasureTheory.Section_1_4_2.Part6


def ConcreteSigmaAlgebra.toMeasurableSpace {X: Type*} (B: ConcreteSigmaAlgebra X) : MeasurableSpace X :=
  B.measurableSpace

def MeasurableSpace.toConcreteSigmaAlgebra {X: Type*} (M: MeasurableSpace X) : ConcreteSigmaAlgebra X :=
  M.sigmaAlgebra

