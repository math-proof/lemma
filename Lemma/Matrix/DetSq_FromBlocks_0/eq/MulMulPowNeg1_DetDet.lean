import sympy.matrices.block_swap
import sympy.Basic
import Lemma.Matrix.DetSq_FromBlocks.eq.MulPowNeg1_DetFromBlocks
open Matrix Equiv Matrix.BlockSwap


@[path]
private lemma main
  [CommRing R]
  {a b : ℕ}
-- given
  (P : Matrix (Fin a) (Fin b) R)
  (A : Matrix (Fin a) (Fin a) R)
  (C : Matrix (Fin b) (Fin b) R) :
-- imply
  (sq (Matrix.fromBlocks P A C 0)).det = (-1) ^ (a * b) * A.det * C.det := by
-- proof
  rw [DetSq_FromBlocks.eq.MulPowNeg1_DetFromBlocks, Matrix.det_fromBlocks_zero₂₁, mul_assoc]


-- created on 2026-10-07
