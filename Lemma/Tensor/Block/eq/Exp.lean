import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Matrix.Block


@[main]
private lemma main
  {A B C D : Matrix (Fin n) (Fin n) ℝ} :
-- imply
  Matrix.fromBlocks (A.map Real.exp) (B.map Real.exp) (C.map Real.exp) (D.map Real.exp) =
    (Matrix.fromBlocks A B C D).map Real.exp :=
-- proof
  (Matrix.fromBlocks_map A B C D Real.exp).symm


-- created on 2023-06-08
