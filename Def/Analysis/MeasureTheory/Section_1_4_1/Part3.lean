module
public import Mathlib.Order.BooleanAlgebra.Defs
public import Def.Analysis.MeasureTheory.Section_1_3_5.Part3
public import Instance.Analysis.MeasureTheory.Section_1_4_1.Part3


public section

def ConcreteBooleanAlgebra.generated_by {X:Type*} (F: Set (Set X)) : ConcreteBooleanAlgebra X :=
  sInf { B | ∀ E ∈ F, B.measurable E }

