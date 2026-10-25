import Mathlib.Order.BooleanAlgebra.Defs
import Def.Analysis.MeasureTheory.Section_1_3_5.Part3
import Instance.Analysis.MeasureTheory.Section_1_4_1


def ConcreteBooleanAlgebra.measurableSets {X:Type*} (B: ConcreteBooleanAlgebra X) : Set (Set X) :=
  { E | B.measurable E }

