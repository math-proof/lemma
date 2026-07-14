import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.EqSwap_0'1
import Lemma.Nat.EqMax.of.Gt
import Lemma.Tensor.Dot.eq.SelectDot_Unsqueeze_1
import Lemma.Tensor.ResizeUnsqueeze_Succ.as.UnsqueezeResize
import Lemma.Tensor.SEqMulS.of.SEq.SEq
import Lemma.Tensor.SEqRepeatS.of.SEq.EqValS.Eq
import Lemma.Tensor.SEqRepeat_1
import Lemma.Tensor.SEqResize.of.Eq_Get
import Lemma.Tensor.SEqSelectS.of.SEq
import Lemma.Tensor.SEqSumS.of.SEq.Eq
import Lemma.Tensor.SEqUnsqueezeS.of.SEq.Eq
import Lemma.Tensor.TransposeUnsqueeze.eq.Unsqueeze
open Bool List Nat Tensor
set_option maxHeartbeats 10000000


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_k : k > k')
  (A : Tensor α [m, k])
  (B : Tensor α [k']) :
-- imply
  let A' : Tensor α [m, 1, k] := A.unsqueeze 1
  let B' : Tensor α [k] := B.resize 0 k
  let B' : Tensor α [1, 1, k] := (B'.unsqueeze 0).unsqueeze 0
  let B' : Tensor α [m, 1, k] := cast (congrArg (Tensor α) (by simp)) (B'.repeat ⟨0, by grind⟩ m)
  A @ B = ((A' * B').sum 2).select ⟨1, by simp⟩ ⟨0, by simp⟩ := by
-- proof
  simp
  rw [Dot.eq.SelectDot_Unsqueeze_1]
  apply Eq.of.SEq
  apply SEqSelectS.of.SEq
  simp [Dot.dot]
  simp [einsum]
  simp [tensordot]
  apply SEqCast.of.SEq.Eq (by simp [matmul_shape])
  simp [matmul, bmm]
  apply SEqCast.of.SEq.Eq (by simp [broadcast_shape])
  apply SEqSumS.of.SEq.Eq (by simp [broadcast_shape])
  apply SEqMulS.of.SEq.SEq
  ·
    apply SEqCast.of.SEq.Eq (by simp [broadcast_shape])
    rw [@Tensor.Repeat_1.eq.Cast]
    apply SEqUnsqueezeS.of.SEq.Eq _ (by simp [broadcast_shape])
    rw [EqMax.of.Gt h_k]
    apply SEqResize.of.Eq_Get (i := ⟨1, by grind⟩)
    rfl
  ·
    apply SEqCastS.of.SEq.Eq.Eq (by simp [broadcast_shape]) (by simp)
    apply SEqRepeatS.of.SEq.EqValS.Eq (by simp) (by simp [broadcast_shape])
    apply SEqUnsqueezeS.of.SEq.Eq _ (by simp [broadcast_shape])
    apply SEqCast.of.SEq.Eq (by simp [broadcast_shape, EqSwap_0'1])
    rw [EqMax.of.Gt h_k]
    have := ResizeUnsqueeze_Succ.eq.Cast_UnsqueezeResize B ⟨0, by grind⟩ k
    simp at this
    rw [this]
    erw [TransposeUnsqueeze.eq.Unsqueeze]
    rfl


-- created on 2026-07-14
