module
public import Mathlib.SetTheory.Cardinal.Aleph
public import Instance.Analysis.MeasureTheory.Section_1_4_1.Part4
public import Def.Analysis.MeasureTheory.Section_1_4_2


public section

theorem ConcreteSigmaAlgebra.isSigmaAlgebra {X: Type*} (B: ConcreteSigmaAlgebra X) : B.isSigmaAlgebra :=
  B.countable_union_mem

