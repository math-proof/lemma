import Def.Analysis.MeasureTheory.Section_1_4_2.Part8
import Def.Analysis.MeasureTheory.Section_1_4_3.Part4


noncomputable instance CountablyAdditiveMeasure.instZero {X:Type*} (B: ConcreteSigmaAlgebra X) : Zero (CountablyAdditiveMeasure B) :=
  {
    zero := {
      toFinitelyAdditiveMeasure := 0
      measure_countable_additive := fun _ _ _ => tsum_zero.symm
    }
  }

noncomputable instance CountablyAdditiveMeasure.instAddCommMonoid {X:Type*} {B: ConcreteSigmaAlgebra X} : AddCommMonoid (CountablyAdditiveMeasure B) :=
{
  add_assoc := by
    intro μ ν ρ
    ext A
    exact add_assoc _ _ _
  zero_add := by
    intro μ
    ext A
    exact zero_add _
  add_zero := by
    intro μ
    ext A
    exact add_zero _
  add_comm := by
    intro μ ν
    ext A
    exact add_comm _ _
  nsmul := nsmulRec
}

