import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.EqSwap_0'1
import Lemma.Nat.EqMax.of.Gt
import Lemma.Tensor.Dot.eq.GetDotUnsqueeze_0
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
import Lemma.Tensor.SEqMulS.of.SEq.SEq
import Lemma.Tensor.SEqRepeatS.of.SEq.EqValS.Eq
import Lemma.Tensor.SEqResize.of.Eq_Get
import Lemma.Tensor.SEqSumS.of.SEq.Eq
import Lemma.Tensor.SEqTS.of.SEq
import Lemma.Tensor.SEqUnsqueezeS.of.SEq.Eq
open Bool List Nat Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h : k > k')
  (A : Tensor α [k])
  (B : Tensor α [k', n]) :
-- imply
  let A' : Tensor α [1, 1, k] := (A.unsqueeze 0).unsqueeze 1
  let A' : Tensor α [1, n, k] := cast (congrArg (Tensor α) (by simp)) (A'.repeat ⟨1, by grind⟩ n)
  let B' : Tensor α [k, n] := B.resize ⟨0, by grind⟩ k
  let B' : Tensor α [n, k] := B'ᵀ
  let B' : Tensor α [1, n, k] := B'.unsqueeze 0
  let B' : Tensor α [1, n, k] := cast (congrArg (Tensor α) (by simp)) (B'.repeat ⟨0, by grind⟩ 1)
  A @ B = ((A' * B').sum 2).get ⟨0, by grind⟩ := by
-- proof
  simp
  rw [Dot.eq.GetDotUnsqueeze_0]
  apply Eq.of.SEq
  apply SEqGetS.of.SEq.GtLength
  simp [Dot.dot]
  simp [Tensor.einsum]
  simp [Tensor.tensordot]
  apply SEqCast.of.SEq.Eq (by simp [matmul_shape])
  simp [Tensor.matmul, bmm]
  apply SEqCast.of.SEq.Eq (by simp [broadcast_shape])
  apply SEqSumS.of.SEq.Eq (by simp [broadcast_shape])
  apply SEqMulS.of.SEq.SEq
  ·
    apply SEqCastS.of.SEq.Eq.Eq (by simp [broadcast_shape]) (by simp)
    apply SEqRepeatS.of.SEq.EqValS.Eq (by simp) (by simp [broadcast_shape])
    apply SEqCast.of.SEq.Eq (by simp [broadcast_shape])
    apply SEqUnsqueezeS.of.SEq.Eq _ (by simp [broadcast_shape])
    rw [EqMax.of.Gt h]
    apply SEqResize.of.Eq_Get (by grind) (i := ⟨1, by grind⟩)
  ·
    apply SEqCastS.of.SEq.Eq.Eq (by simp [broadcast_shape]) (by simp)
    apply SEqRepeatS.of.SEq.EqValS.Eq (by simp) (by simp [broadcast_shape])
    apply SEqUnsqueezeS.of.SEq.Eq _ (by simp [broadcast_shape])
    apply SEqCast.of.SEq.Eq (by simp [broadcast_shape, EqSwap_0'1])
    apply SEqTS.of.SEq
    rw [EqMax.of.Gt h]
    rfl


-- created on 2026-07-14
