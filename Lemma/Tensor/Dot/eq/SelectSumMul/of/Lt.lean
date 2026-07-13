import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.EqSwap_0'1
import Lemma.Tensor.Dot.eq.SelectDot_Unsqueeze_1
import Lemma.Tensor.SEqMulS.of.SEq.SEq
import Lemma.Tensor.SEqRepeatS.of.SEq.EqValS.Eq
import Lemma.Tensor.SEqRepeat_1
import Lemma.Tensor.SEqResize.of.Eq_Get
import Lemma.Tensor.SEqResize_0.of.Eq_Get_0.GtLength_0
import Lemma.Tensor.SEqSelectS.of.SEq
import Lemma.Tensor.SEqSumS.of.SEq.Eq
import Lemma.Tensor.SEqUnsqueezeS.of.SEq.Eq
import Lemma.Tensor.TransposeCast.as.Transpose.of.Eq
import Lemma.Tensor.TransposeUnsqueeze.eq.Unsqueeze
open Bool List Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_k : k' < k)
  (A : Tensor α [m, k'])
  (B : Tensor α [k]) :
-- imply
  let A' : Tensor α [m, k] := A.resize 1 k
  let A' : Tensor α [m, 1, k] := A'.unsqueeze 1
  let B' : Tensor α [1, 1, k] := (B.unsqueeze 0).unsqueeze 0
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
    apply SEqResize.of.Eq_Get (i := ⟨1, by grind⟩) (by simp)
  ·
    apply SEqCastS.of.SEq.Eq.Eq (by simp [broadcast_shape]) (by simp)
    apply SEqRepeatS.of.SEq.EqValS.Eq (by simp) (by simp [broadcast_shape])
    apply SEqUnsqueezeS.of.SEq.Eq _ (by simp [broadcast_shape])
    apply SEqCast.of.SEq.Eq (by simp [broadcast_shape, EqSwap_0'1])
    erw [Resize_0.eq.Cast.of.Eq_Get_0.GtLength_0 (by simp) (by grind)]
    erw [TransposeCast.eq.Cast_Transpose.of.Eq.t (by simp [broadcast_shape])]
    apply SEqCast.of.SEq.Eq (by simp [broadcast_shape, EqSwap_0'1])
    apply SEq.of.Eq
    apply TransposeUnsqueeze.eq.Unsqueeze


-- created on 2026-07-13
