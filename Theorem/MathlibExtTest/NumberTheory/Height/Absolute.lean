/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Height/Absolute.lean -/


import Def.NumberTheory.Height.Absolute
import Lemma.Nat.Height.Absolute


namespace HeightTest

open NumberField

variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]

example (x : K) : NumberField.primitiveIntMinpoly x ≠ 0 :=
  NumberField.primitiveIntMinpoly_ne_zero x

example (x : K) : (NumberField.primitiveIntMinpoly x).IsPrimitive :=
  NumberField.primitiveIntMinpoly_isPrimitive x

example (x : K) :
    (NumberField.primitiveIntMinpoly x).natDegree = (minpoly ℚ x).natDegree :=
  NumberField.primitiveIntMinpoly_natDegree x

example {L : Type*} [Field L] [CharZero L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L]
    (f : K →ₐ[ℚ] L) (hf : Function.Injective f) (x : K) :
    NumberField.primitiveIntMinpoly (f x) = NumberField.primitiveIntMinpoly x :=
  NumberField.primitiveIntMinpoly_algHom_eq f hf x

example (x : K) : 0 < NumberField.absMulHeight₁ x :=
  NumberField.absMulHeight₁_pos x

example (x : K) : 1 ≤ NumberField.absMulHeight₁ x :=
  NumberField.one_le_absMulHeight₁ x

example (x : K) : 0 ≤ NumberField.absLogHeight₁ x :=
  NumberField.absLogHeight₁_nonneg x

example : 0 < NumberField.absMulHeight₁ (0 : ℚ) := by
  exact NumberField.absMulHeight₁_pos 0

example : 0 ≤ NumberField.absLogHeight₁ (-1 : ℚ) := by
  exact NumberField.absLogHeight₁_nonneg (-1)

end HeightTest
