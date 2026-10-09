import Mathlib
import sympy.Basic

open NumberField NumberField.mixedEmbedding Module
open scoped Classical

/--
[NumberField_mixedEmbedding_trace_mixedEmbedding](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_NumberField_mixedEmbedding_trace_mixedEmbedding.lean)
-/
@[path]
private lemma main
  [Field K] [NumberField K]
  {x : K} :
-- imply
  Algebra.trace ℝ (mixedSpace K) (mixedEmbedding K x) = (Algebra.trace ℚ K x : ℝ) := by
-- proof
  rw [Algebra.trace_eq_matrix_trace (latticeBasis K) (mixedEmbedding K x),
    Algebra.trace_eq_matrix_trace (integralBasis K) x, Matrix.trace, Matrix.trace, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, latticeBasis_apply, ← map_mul, latticeBasis_repr_apply]


-- created on 2026-10-05
