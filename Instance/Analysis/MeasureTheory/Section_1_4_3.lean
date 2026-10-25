import Def.Analysis.MeasureTheory.Section_1_4_2.Part8
import Def.Analysis.MeasureTheory.Section_1_4_3


/-- Example 1.4.23 (Zero measure) -/
noncomputable instance FinitelyAdditiveMeasure.instZero {X:Type*} (B: ConcreteBooleanAlgebra X) : Zero (FinitelyAdditiveMeasure B) :=
  {
    zero := {
      measure := fun A => 0
      measure_pos := fun _ _ => le_rfl
      measure_empty := rfl
      measure_finite_additive := fun _ _ _ _ _ => by simp
    }
  }

/-- Example 1.4.24 (linear combinations of measures) -/
noncomputable instance FinitelyAdditiveMeasure.instAdd {X:Type*} {B: ConcreteBooleanAlgebra X} : Add (FinitelyAdditiveMeasure B) :=
  {
    add := fun μ ν =>
      {
        measure := fun A => μ.measure A + ν.measure A
        measure_pos := fun A hA => add_nonneg (μ.measure_pos A hA) (ν.measure_pos A hA)
        measure_empty := by simp [μ.measure_empty, ν.measure_empty]
        measure_finite_additive := fun E F hE hF hdisj => by
          simp [μ.measure_finite_additive E F hE hF hdisj,
            ν.measure_finite_additive E F hE hF hdisj]
          abel
      }
  }

noncomputable instance FinitelyAdditiveMeasure.instSmul {X:Type*} {B: ConcreteBooleanAlgebra X} : SMul ENNReal (FinitelyAdditiveMeasure B) :=
{
    smul := fun c μ =>
        {
        measure := fun A => c * μ.measure A
        measure_pos := fun A hA => mul_nonneg (EReal.coe_ennreal_nonneg c) (μ.measure_pos A hA)
        measure_empty := by simp [μ.measure_empty]
        measure_finite_additive := fun E F hE hF hdisj => by
          rw [μ.measure_finite_additive E F hE hF hdisj]
          exact EReal.left_distrib_of_nonneg (μ.measure_pos E hE) (μ.measure_pos F hF)
        }
}

noncomputable instance FinitelyAdditiveMeasure.instAddCommMonoid {X:Type*} {B: ConcreteBooleanAlgebra X} : AddCommMonoid (FinitelyAdditiveMeasure B) :=
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

