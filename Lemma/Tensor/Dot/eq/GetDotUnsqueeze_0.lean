import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Tensor.Dot.eq.SumMul
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
import Lemma.Tensor.Matmul.as.Bmm
import Lemma.Tensor.SEqBatchDotS.of.SEq.SEq
import Lemma.Tensor.SEqBroadcastS.of.SEq.Eq.Dvd
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
import Lemma.Tensor.SEqResize.of.Eq_Get
import Lemma.Tensor.SEqResize_0.of.Eq_Get_0.GtLength_0
import Lemma.Tensor.Select_0.as.Get.of.Lt_Get_0.GtLength_0
open Bool Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (A : Tensor α [k])
  (B : Tensor α [k, n]) :
-- imply
  A @ B = ((A.unsqueeze 0) @ B).get ⟨0, GtLengthDot.of.LeLengthS.Ne_Nil (by grind) (by grind) _ _ (i := ⟨0, by simp⟩)⟩ := by
-- proof
  have h := Dot.eq.SumMul (A.unsqueeze 0) B
  simp at h
  simp [Dot.dot]
  simp [Tensor.einsum]
  apply EqCast.of.SEq.Eq (by simp [matmul_shape])
  erw [Select_0.eq.Cast_Get.of.Lt_Get_0.GtLength_0 (by grind) (by grind)]
  apply SEqCast.of.SEq.Eq (by simp)
  apply SEqGetS.of.SEq.GtLength (by grind)
  simp [Tensor.tensordot]
  apply SEq_Cast.of.SEq.Eq (by simp [broadcast_shape, matmul_shape])
  rw [Matmul.eq.Cast_Bmm]
  apply SEq_Cast.of.SEq.Eq (by simp [broadcast_shape])
  apply SEqBatchDotS.of.SEq.SEq _ (by rfl)
  symm
  have := SEqResize.of.Eq_Get (by grind) (A.unsqueeze 0) (i := ⟨1, by grind⟩) (n := k ⊔ k)
  apply this.trans
  unfold unsqueeze
  apply SEqBroadcastS.of.SEq.Eq.Dvd (by simp) (by simp)
  symm
  apply SEqResize_0.of.Eq_Get_0.GtLength_0 (by simp) (by simp)


-- created on 2026-07-10
