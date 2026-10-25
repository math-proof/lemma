import Mathlib
import sympy.Basic
import Def.LinearAlgebra.QuadraticForm.System
open QuadraticForm


namespace QuadraticForm

/--
[systemOrthogonalSum_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/QuadraticForm/System.lean)
-/
@[path]
lemma systemOrthogonalSum_apply
  [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
  {Q : ι → QuadraticForm R M}
  {Q' : ι → QuadraticForm R N}
  {i : ι}
  {x : M × N} :
-- imply
  systemOrthogonalSum Q Q' i x = Q i x.1 + Q' i x.2 := by
-- proof
  simp [systemOrthogonalSum]

end QuadraticForm

namespace QuadraticForm

/--
[systemOrthogonalSum_inl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/QuadraticForm/System.lean)
-/
@[path]
lemma systemOrthogonalSum_inl
  [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
  {Q : ι → QuadraticForm R M}
  {Q' : ι → QuadraticForm R N}
  {i : ι}
  {x : M} :
-- imply
  systemOrthogonalSum Q Q' i (x, 0) = Q i x := by
-- proof
  simp

end QuadraticForm

namespace QuadraticForm

/--
[systemOrthogonalSum_inr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/QuadraticForm/System.lean)
-/
@[path]
lemma systemOrthogonalSum_inr
  [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
  {Q : ι → QuadraticForm R M}
  {Q' : ι → QuadraticForm R N}
  {i : ι}
  {y : N} :
-- imply
  systemOrthogonalSum Q Q' i (0, y) = Q' i y := by
-- proof
  simp

end QuadraticForm


-- created on 2026-10-20
-- updated on 2026-10-23
