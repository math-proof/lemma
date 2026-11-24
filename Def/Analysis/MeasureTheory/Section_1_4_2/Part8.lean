module
public import Mathlib.SetTheory.Cardinal.Aleph
public import Instance.Analysis.MeasureTheory.Section_1_4_1.Part4
public import Theorem.Analysis.MeasureTheory.Section_1_4_2.Part6


public section

def ConcreteSigmaAlgebra.toMeasurableSpace {X: Type*} (B: ConcreteSigmaAlgebra X) : MeasurableSpace X :=
  B.measurableSpace

def MeasurableSpace.toConcreteSigmaAlgebra {X: Type*} (M: MeasurableSpace X) : ConcreteSigmaAlgebra X :=
  M.sigmaAlgebra

