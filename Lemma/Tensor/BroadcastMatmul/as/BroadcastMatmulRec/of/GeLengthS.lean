import Lemma.Tensor.BroadcastMatmul.as.BroadcastMatmulRec.of.GtLengthS
import Lemma.Tensor.BroadcastMatmul.eq.BroadcastMatmulRec.of.EqLengthS
import Lemma.Tensor.SEqBroadcast.of.Eq
import Lemma.Tensor.SEqBroadcastMatmulRecS.of.SEq.SEq
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
  X.broadcast_matmul Y ≃ X.broadcast_matmul_rec (Y.broadcast (s.take (s.length - s'.length) ++ s' ++ [n, k]) (by simp)) (by grind) := by
-- proof
  if h : s.length = s'.length then
    rw [BroadcastMatmul.eq.BroadcastMatmulRec.of.EqLengthS h]
    apply SEqBroadcastMatmulRecS.of.SEq.SEq
    ·
      assumption
    ·
      rfl
    ·
      rw [← h]
      apply SEq_Broadcast.of.Eq
      simp
  else
    apply BroadcastMatmul.as.BroadcastMatmulRec.of.GtLengthS
    omega


-- created on 2026-01-12
