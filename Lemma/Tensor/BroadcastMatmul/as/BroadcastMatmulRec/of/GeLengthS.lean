import Lemma.Tensor.ReshapeMatmul.as.BroadcastMatmulRec.of.GtLengthS
import Lemma.Tensor.ReshapeMatmul.eq.BroadcastMatmulRec.of.EqLengthS
import Lemma.Tensor.SEqReshape.of.Eq
import Lemma.Tensor.SEqReshapeMatmulRecS.of.SEq.SEq
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
    rw [ReshapeMatmul.eq.BroadcastMatmulRec.of.EqLengthS h]
    apply SEqReshapeMatmulRecS.of.SEq.SEq
    ·
      assumption
    ·
      rfl
    ·
      rw [← h]
      apply SEq_Reshape.of.Eq
      simp
  else
    apply ReshapeMatmul.as.BroadcastMatmulRec.of.GtLengthS
    omega


-- created on 2026-01-12
