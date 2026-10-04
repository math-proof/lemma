import sympy.Basic
import Mathlib.Data.Matrix.Block


@[main]
private lemma main
  {n : ℕ}
  {A B C D : Matrix (Fin n) (Fin n) ℝ} :
-- imply
  Matrix.fromBlocks (A.map Real.sin) (B.map Real.sin) (C.map Real.sin) (D.map Real.sin)
    = (Matrix.fromBlocks A B C D).map Real.sin :=
-- proof
  (Matrix.fromBlocks_map A B C D Real.sin).symm


-- created on 2023-06-08
