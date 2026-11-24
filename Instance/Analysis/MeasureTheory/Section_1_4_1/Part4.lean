module
public import Mathlib.Order.BooleanAlgebra.Defs
public import Def.Analysis.MeasureTheory.Section_1_3_5.Part3
public import Def.Analysis.MeasureTheory.Section_1_4_1.Part3


public section

/-- Definition 1.4.10 (Generation of algebras) -/
instance ConcreteBooleanAlgebra.instSupSet {X:Type*} : SupSet (ConcreteBooleanAlgebra X) :=
  {
      sSup S := ConcreteBooleanAlgebra.generated_by (⋃ B ∈ S, B.measurableSets)
  }

