import Lemma.Tensor.Tensordot.as.Matmul.of.GtLengthS
import Lemma.Tensor.Tensordot.eq.Matmul.of.EqLengthS
import Lemma.Tensor.SEqReshape.of.Eq
import Lemma.Tensor.SEqMatmulS.of.SEq.SEq
open Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
  {s s' : List ℕ}
-- given
  (h : s.length ≥ s'.length)
  (X : Tensor α (s ++ [m, n]))
  (Y : Tensor α (s' ++ [n, k])) :
-- imply
  X.tensordot Y ≃ X.matmul (Y.reshape (s.take (s.length - s'.length) ++ s' ++ [n, k]) (by simp)) (by grind) := by
-- proof
  if h : s.length = s'.length then
    rw [Tensordot.eq.Matmul.of.EqLengthS h]
    apply SEqMatmulS.of.SEq.SEq
    ·
      assumption
    ·
      rfl
    ·
      rw [← h]
      apply SEq_Reshape.of.Eq
      simp
  else
    apply Tensordot.as.Matmul.of.GtLengthS
    omega


-- created on 2026-01-12
