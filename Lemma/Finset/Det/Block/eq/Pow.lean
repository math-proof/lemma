import sympy.matrices.block_swap
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n m : ℕ} :
-- imply
  (Matrix.BlockSwap.sq (Matrix.fromBlocks (0 : Matrix (Fin n) (Fin m) ℂ) 1 1 0)).det = (-1) ^ (n * m) := by
-- proof
  rw [Matrix.BlockSwap.det_zero₁₁, Matrix.det_one, Matrix.det_one, mul_one, mul_one]


-- created on 2026-09-27
