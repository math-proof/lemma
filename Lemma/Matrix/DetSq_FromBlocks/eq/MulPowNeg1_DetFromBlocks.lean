import sympy.matrices.block_swap
import sympy.Basic
import Lemma.Matrix.SignTau.eq.PowNeg1Mul
open Matrix Equiv Matrix.BlockSwap


@[path]
private lemma main
  [CommRing R]
  {a b : ℕ}
-- given
  (P : Matrix (Fin a) (Fin b) R)
  (Q : Matrix (Fin a) (Fin a) R)
  (C : Matrix (Fin b) (Fin b) R)
  (S : Matrix (Fin b) (Fin a) R) :
-- imply
  (sq (Matrix.fromBlocks P Q C S)).det = (-1) ^ (a * b) * (Matrix.fromBlocks Q P S C).det := by
-- proof
  have h : sq (Matrix.fromBlocks P Q C S) =
      (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks Q P S C)).submatrix id (tau a b) := by
    ext i j
    simp only [BlockSwap.sq, BlockSwap.tau, Matrix.of_apply, Matrix.submatrix_apply, Matrix.reindex_apply, id, Equiv.trans_apply,
      finCongr_apply, Equiv.symm_apply_apply]
    rcases finSumFinEquiv.symm i with r | r <;>
      rcases hc : finSumFinEquiv.symm (Fin.cast (Nat.add_comm a b) j) with k | k <;> simp
  rw [h, Matrix.det_permute', Matrix.det_reindex_self, SignTau.eq.PowNeg1Mul]
  push_cast
  ring


-- created on 2026-10-07
