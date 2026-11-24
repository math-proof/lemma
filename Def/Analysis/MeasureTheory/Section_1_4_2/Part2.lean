module
public import Mathlib.SetTheory.Cardinal.Aleph
public import Instance.Analysis.MeasureTheory.Section_1_4_1.Part4
public import Theorem.Analysis.MeasureTheory.Section_1_4_2


public section

def ConcreteBooleanAlgebra.isSigmaAlgebra.toSigmaAlgebra {X: Type*} {B: ConcreteBooleanAlgebra X} (h: B.isSigmaAlgebra) : ConcreteSigmaAlgebra X :=
  { toConcreteBooleanAlgebra := B
    countable_union_mem := h }

