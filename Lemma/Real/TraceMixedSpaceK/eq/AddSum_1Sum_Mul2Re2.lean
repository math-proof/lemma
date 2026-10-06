import Mathlib
import sympy.Basic

open NumberField NumberField.mixedEmbedding

/--
[NumberField_mixedEmbedding_trace_mixedSpace_apply](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_NumberField_mixedEmbedding_trace_mixedSpace_apply.lean)
-/

private lemma  trace_pi_self (k : Type*) [Field k] (ι : Type*) [Fintype ι] [DecidableEq ι] (z : ι → k) :
    Algebra.trace k (ι → k) z = ∑ i, z i := by
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun k ι), Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Pi.basisFun_repr, Pi.basisFun_apply, Pi.mul_apply,
    Pi.single_eq_same, mul_one]


open scoped Classical in
@[main]
private lemma main
  [Field K] [NumberField K]
  {z : mixedSpace K} :
-- imply
  Algebra.trace ℝ (mixedSpace K) z =
      (∑ w : {w : InfinitePlace K // w.IsReal}, z.1 w) +
        ∑ w : {w : InfinitePlace K // w.IsComplex}, 2 * (z.2 w).re := by
-- proof
  classical
  rw [Algebra.trace_prod_apply, trace_pi_self]
  congr 1
  rw [← Algebra.trace_trace (S := ℂ), trace_pi_self, Algebra.trace_complex_apply, Complex.re_sum,
    Finset.mul_sum]


-- created on 2026-10-05
