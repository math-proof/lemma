/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/QuadraticForm/System.lean -/

import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Systems of quadratic forms

This file defines the pointwise orthogonal sum of two systems of quadratic
forms with the same index type.
-/

namespace QuadraticForm

variable {R M N ι : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-- The pointwise orthogonal sum of two equally indexed systems of quadratic forms. -/
def systemOrthogonalSum (Q : ι → QuadraticForm R M) (Q' : ι → QuadraticForm R N) :
    ι → QuadraticForm R (M × N) :=
  fun i ↦ (Q i).prod (Q' i)

/-- Evaluation of a pointwise orthogonal sum. -/
@[simp]
theorem systemOrthogonalSum_apply (Q : ι → QuadraticForm R M)
    (Q' : ι → QuadraticForm R N) (i : ι) (x : M × N) :
    systemOrthogonalSum Q Q' i x = Q i x.1 + Q' i x.2 := by
  simp [systemOrthogonalSum]

/-- The left summand restricts to the original left-hand system. -/
@[simp]
theorem systemOrthogonalSum_inl (Q : ι → QuadraticForm R M)
    (Q' : ι → QuadraticForm R N) (i : ι) (x : M) :
    systemOrthogonalSum Q Q' i (x, 0) = Q i x := by
  simp

/-- The right summand restricts to the original right-hand system. -/
@[simp]
theorem systemOrthogonalSum_inr (Q : ι → QuadraticForm R M)
    (Q' : ι → QuadraticForm R N) (i : ι) (y : N) :
    systemOrthogonalSum Q Q' i (0, y) = Q' i y := by
  simp

end QuadraticForm
