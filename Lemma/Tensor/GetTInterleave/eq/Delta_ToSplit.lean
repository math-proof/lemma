import torch.Tensor.permute
import Lemma.Tensor.GetInterleave.eq.Delta_ToSplit
import Lemma.Tensor.EqGetT
open Bool Tensor Fin


@[path]
private lemma main
-- given
  (i k : Fin (d + d)) :
-- imply
  (cast (congrArg (Tensor ℝ) (a₂ := [d + d, d + d]) (by simp)) (interleave d)ᵀ)[i][k] =
    (↑(KroneckerDelta (k : ℕ) i.toSplit) : Tensor ℝ []) := by
-- proof
  apply (Eq.of.SEq (SEqGetS.of.SEq.GtLength (by simp [Tensor.length]) (GetCast.as.Get.of.Eq.GtLength_0.right.fin (s' := [d + d, d + d]) (by simp) (by simp) _ i))).trans
  apply (EqGetT.fin (interleave d) k i).trans
  apply GetInterleave.eq.Delta_ToSplit


-- created on 2026-09-05
