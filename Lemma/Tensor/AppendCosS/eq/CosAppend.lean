import sympy.Basic
import Mathlib.Data.Matrix.Block


@[main]
private lemma main
  {n : ℕ}
  {A B C D : Matrix (Fin n) (Fin n) ℝ} :
-- imply
  Matrix.fromBlocks (A.map Real.cos) (B.map Real.cos) (C.map Real.cos) (D.map Real.cos)
    = (Matrix.fromBlocks A B C D).map Real.cos :=
-- proof
  (Matrix.fromBlocks_map A B C D Real.cos).symm


-- created on 2023-06-08
