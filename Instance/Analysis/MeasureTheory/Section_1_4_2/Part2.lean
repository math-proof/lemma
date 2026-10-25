import Mathlib.SetTheory.Cardinal.Aleph
import Instance.Analysis.MeasureTheory.Section_1_4_1.Part4
import Def.Analysis.MeasureTheory.Section_1_4_2.Part5


/-- Definition 1.4.14 (Generation of σ-algebras) -/
instance ConcreteSigmaAlgebra.instSupSet {X:Type*} : SupSet (ConcreteSigmaAlgebra X) :=
  {
      sSup S := ConcreteSigmaAlgebra.generated_by (⋃ B ∈ S, B.measurableSets)
  }

