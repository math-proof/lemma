import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.MatrixExpDetTrace
open scoped BigOperators
open MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted


/--
[matrix_det_exp_eq_exp_trace](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MatrixExpDetTrace.lean)
-/
@[path]
private lemma matrix_det_exp_eq_exp_trace_eq
  [Fintype n] [DecidableEq n]
  {A : Matrix n n ℂ} :
-- imply
  Matrix.det (NormedSpace.exp A) = Complex.exp (Matrix.trace A) := by
-- proof
  apply MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted.matrix_det_exp_eq_exp_trace A

/--
[matrix_exp_eq_sum_of_isNilpotent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MatrixExpDetTrace.lean)
-/
@[path]
private lemma matrix_exp_eq_sum_of_isNilpotent_eq
  [Fintype n] [DecidableEq n]
  {A : Matrix n n ℂ}
-- given
  (h : IsNilpotent A) :
-- imply
  ∃ m : ℕ, NormedSpace.exp A = ∑ k ∈ Finset.range m, (Nat.factorial k : ℂ)⁻¹ • A ^ k := by
-- proof
  apply MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted.matrix_exp_eq_sum_of_isNilpotent A h


-- created on 2026-10-20
