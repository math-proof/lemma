module
public import Mathlib.Order.BooleanAlgebra.Defs
public import Def.Analysis.MeasureTheory.Section_1_3_5.Part3
public import Instance.Analysis.MeasureTheory.Section_1_4_1


public section

def ConcreteBooleanAlgebra.measurableSets {X:Type*} (B: ConcreteBooleanAlgebra X) : Set (Set X) :=
  { E | B.measurable E }

