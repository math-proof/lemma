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

end QuadraticForm
