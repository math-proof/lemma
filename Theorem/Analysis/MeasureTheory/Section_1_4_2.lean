import Mathlib.SetTheory.Cardinal.Aleph
import Instance.Analysis.MeasureTheory.Section_1_4_1.Part4
import Def.Analysis.MeasureTheory.Section_1_4_2


theorem ConcreteSigmaAlgebra.isSigmaAlgebra {X: Type*} (B: ConcreteSigmaAlgebra X) : B.isSigmaAlgebra :=
  B.countable_union_mem

