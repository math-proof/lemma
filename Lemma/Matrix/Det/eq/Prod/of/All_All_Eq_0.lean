import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [CommRing R]
  {n : ℕ}
  {M : Matrix (Fin n) (Fin n) R}
-- given
  (h : ∀ i j : Fin n, i < j → M i j = 0) :
-- imply
  M.det = ∏ i, M i i :=
-- proof
  Matrix.det_of_isLowerTriangular M fun i j hij => h i j hij


-- created on 2026-10-07
