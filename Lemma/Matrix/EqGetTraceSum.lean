import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.LieGroups.code.SchurOrthogonality
open MeasureTheory ContinuousRep
open scoped ComplexConjugate


/--
[trace_eq_sum_inner](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SchurOrthogonality.lean)
-/
@[path]
lemma trace_eq_sum_inner
  [Group K]
  [TopologicalSpace K]
  [IsTopologicalGroup K]
  [Fintype ι]
  [DecidableEq ι]
  [NormedAddCommGroup E]
  [InnerProductSpace ℂ E]
  {b : OrthonormalBasis ι ℂ E}
  {L : E →ₗ[ℂ] E} :
-- imply
  (LinearMap.trace ℂ E) L = ∑ i, @inner ℂ _ _ (b i) (L (b i)) := by
-- proof
  rw [LinearMap.trace_eq_matrix_trace ℂ b.toBasis]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  congr 1; ext i
  rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  simp [OrthonormalBasis.coe_toBasis]


-- created on 2026-10-23
