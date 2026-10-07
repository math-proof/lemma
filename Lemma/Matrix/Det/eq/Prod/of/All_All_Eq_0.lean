import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
-- given
  (M : Matrix (Fin n) (Fin n) ℝ)
  (h : ∀ i j : Fin n, i < j → M i j = 0) :
-- imply
  M.det = ∏ i, M i i := by
-- proof
  exact Matrix.det_of_isLowerTriangular M fun i j hij => h i j hij


-- created on 2026-10-07
