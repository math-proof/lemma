import Lemma.Tensor.Unsqueeze.eq.Reshape
import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Tensor.Matmul.as.Bmm
import Lemma.Tensor.SEqBmmS.of.SEq.SEq
import Lemma.Tensor.SEqReshapeS.of.SEq.Eq.Dvd
import Lemma.Tensor.SEqResize.of.Eq_Get
import Lemma.Tensor.SEqResize_0.of.Eq_Get_0.GtLength_0
import Lemma.Tensor.SEqSelectS.of.SEq
open Bool Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (A : Tensor α [m, k'])
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
  apply SEqBmmS.of.SEq.SEq (by rfl)
  symm
  if h_k : k' ≤ k then
    have := SEqResize.of.Eq_Get (by simp; grind) (B.unsqueeze 1) (i := ⟨0, by grind⟩) (n := k' ⊔ k)
    simp
    apply this.trans
    unfold unsqueeze
    apply SEqReshapeS.of.SEq.Eq.Dvd (by simp) (by grind)
    symm
    apply SEqResize_0.of.Eq_Get_0.GtLength_0 (by simp) (by grind)
  else
    have h_k : k' > k := by grind
    have := Tensor.Reshape.eq.Unsqueeze (B.resize 0 (k' ⊔ k)) 1
    simp at this
    erw [this]
    rw [Tensor.ResizeUnsqueeze.as.UnsqueezeResize]
    sorry


-- created on 2026-07-11
