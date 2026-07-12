import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Tensor.Matmul.as.Bmm
import Lemma.Tensor.SEqBatchDotS.of.SEq.SEq
import Lemma.Tensor.SEqReshapeS.of.SEq.Eq.Dvd
import Lemma.Tensor.SEqResize.of.Eq_Get
import Lemma.Tensor.SEqResize_0.of.Eq_Get_0.GtLength_0
import Lemma.Tensor.SEqSelectS.of.SEq
open Bool Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (A : Tensor α [m, k])
  (B : Tensor α [k]) :
-- imply
  A @ B = (A @ (B.unsqueeze 1)).select ⟨1, by simp [matmul_shape]⟩ ⟨0, by simp [matmul_shape, broadcast_shape]⟩ := by
-- proof
  simp [Dot.dot]
  simp [Tensor.einsum]
  apply EqCast.of.SEq.Eq (by simp [matmul_shape])
  apply SEqSelectS.of.SEq
  simp [Tensor.tensordot]
  apply SEq_Cast.of.SEq.Eq (by simp [broadcast_shape, matmul_shape])
  rw [Matmul.eq.Cast_Bmm]
  apply SEq_Cast.of.SEq.Eq (by simp [broadcast_shape])
  apply SEqBatchDotS.of.SEq.SEq (by rfl)
  symm
  have := SEqResize.of.Eq_Get (by grind) (B.unsqueeze 1) (i := ⟨0, by grind⟩) (n := k ⊔ k)
  apply this.trans
  unfold unsqueeze
  apply SEqReshapeS.of.SEq.Eq.Dvd (by simp) (by simp)
  symm
  apply SEqResize_0.of.Eq_Get_0.GtLength_0 (by simp) (by simp)


-- created on 2026-07-11
