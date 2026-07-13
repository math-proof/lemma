import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
import Lemma.Tensor.Matmul.as.Bmm
import Lemma.Tensor.ResizeUnsqueeze.as.UnsqueezeResize
import Lemma.Tensor.SEqBmmS.of.SEq.SEq
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
import Lemma.Tensor.Select_0.as.Get.of.GtGet_0.GtLength_0
import Lemma.Tensor.Unsqueeze.eq.Reshape
open Bool Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (A : Tensor α [k'])
  (B : Tensor α [k, n]) :
-- imply
  A @ B = ((A.unsqueeze 0) @ B).get ⟨0, GtLengthDot.of.LeLengthS.Ne_Nil (by grind) (by grind) _ _ (i := ⟨0, by simp⟩)⟩ := by
-- proof
  simp [Dot.dot]
  simp [Tensor.einsum]
  apply EqCast.of.SEq.Eq (by simp [matmul_shape])
  erw [Select_0.eq.Cast_Get.of.GtGet_0.GtLength_0 (by grind) (by grind)]
  apply SEqCast.of.SEq.Eq (by simp)
  apply SEqGetS.of.SEq.GtLength (by grind)
  simp [Tensor.tensordot]
  apply SEq_Cast.of.SEq.Eq (by simp [broadcast_shape, matmul_shape])
  rw [Matmul.eq.Cast_Bmm]
  apply SEq_Cast.of.SEq.Eq (by simp [broadcast_shape])
  apply SEqBmmS.of.SEq.SEq _ (by rfl)
  have := Reshape.eq.Unsqueeze (A.resize 0 (k' ⊔ k)) 0
  simp at this
  erw [this]
  apply UnsqueezeResize.as.ResizeUnsqueeze A ⟨0, by grind⟩


-- created on 2026-07-10
-- updated on 2026-07-11
