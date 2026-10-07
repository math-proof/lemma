import sympy.matrices.block_swap
import sympy.Basic
import Lemma.Matrix.DetSq_FromBlocks.eq.MulPowNeg1_DetFromBlocks
open Matrix Equiv Matrix.BlockSwap


@[main]
private lemma main
  [CommRing R]
  {a b : ℕ}
-- given
  (A : Matrix (Fin a) (Fin a) R)
  (C : Matrix (Fin b) (Fin b) R)
  (D : Matrix (Fin b) (Fin a) R) :
-- imply
  (sq (Matrix.fromBlocks 0 A C D)).det = (-1) ^ (a * b) * A.det * C.det := by
-- proof
  rw [DetSq_FromBlocks.eq.MulPowNeg1_DetFromBlocks, Matrix.det_fromBlocks_zero₁₂, mul_assoc]


-- created on 2026-10-07
