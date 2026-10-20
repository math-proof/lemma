import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.QuadraticForm.System
open QuadraticForm


/--
[systemOrthogonalSum_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/QuadraticForm/System.lean)
-/
@[path]
private lemma systemOrthogonalSum_apply_eq
  [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
  {Q : ι → QuadraticForm R M}
  {Q' : ι → QuadraticForm R N}
  {i : ι}
  {x : M × N} :
-- imply
  systemOrthogonalSum Q Q' i x = Q i x.1 + Q' i x.2 := by
-- proof
  apply QuadraticForm.systemOrthogonalSum_apply Q Q' i x

/--
[systemOrthogonalSum_inl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/QuadraticForm/System.lean)
-/
@[path]
private lemma systemOrthogonalSum_inl_eq
  [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
  {Q : ι → QuadraticForm R M}
  {Q' : ι → QuadraticForm R N}
  {i : ι}
  {x : M} :
-- imply
  systemOrthogonalSum Q Q' i (x, 0) = Q i x := by
-- proof
  apply QuadraticForm.systemOrthogonalSum_inl Q Q' i x

/--
[systemOrthogonalSum_inr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/QuadraticForm/System.lean)
-/
@[path]
private lemma systemOrthogonalSum_inr_eq
  [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
  {Q : ι → QuadraticForm R M}
  {Q' : ι → QuadraticForm R N}
  {i : ι}
  {y : N} :
-- imply
  systemOrthogonalSum Q Q' i (0, y) = Q' i y := by
-- proof
  apply QuadraticForm.systemOrthogonalSum_inr Q Q' i y


-- created on 2026-10-20
