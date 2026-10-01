import sympy.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Block


@[main]
private lemma main
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing α]
-- given
  (X : Matrix m n α) :
-- imply
  (Matrix.fromBlocks (1 : Matrix m m α) X (0 : Matrix n m α) (1 : Matrix n n α))⁻¹ =
    Matrix.fromBlocks (1 : Matrix m m α) (-X) (0 : Matrix n m α) (1 : Matrix n n α) := by
-- proof
  apply Matrix.inv_eq_left_inv
  simp [Matrix.fromBlocks_multiply]


-- created on 2023-07-11
