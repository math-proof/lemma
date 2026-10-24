/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/QuadraticForm/System.lean -/


import sympy.atlas.LinearAlgebra.QuadraticForm.System
import Lemma.Matrix.QuadraticForm.System

namespace QuadraticForm

variable {R M N ι : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

example (Q : ι → QuadraticForm R M) (Q' : ι → QuadraticForm R N)
    (i : ι) (x : M) (y : N) :
    systemOrthogonalSum Q Q' i (x, y) = Q i x + Q' i y := by
  simp

example (Q : ι → QuadraticForm R M) (Q' : ι → QuadraticForm R N)
    (i : ι) (x : M) : systemOrthogonalSum Q Q' i (x, 0) = Q i x := by
  simp

example (Q : ι → QuadraticForm R M) (Q' : ι → QuadraticForm R N)
    (i : ι) (y : N) : systemOrthogonalSum Q Q' i (0, y) = Q' i y := by
  simp

example (i : ι) :
    systemOrthogonalSum (fun _ ↦ (0 : QuadraticForm R M))
      (fun _ ↦ (0 : QuadraticForm R N)) i = 0 := by
  ext x
  simp

end QuadraticForm
