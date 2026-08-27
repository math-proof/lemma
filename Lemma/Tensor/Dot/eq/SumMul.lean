import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Tensor.Dot.eq.Bmm
import Lemma.Tensor.SEqMulS.of.SEq.SEq
import Lemma.Tensor.SEqRepeatS.of.SEq.Val.Eq
import Lemma.Tensor.SEqResizeS.of.SEq.Val.Eq
import Lemma.Tensor.SEqSumS.of.SEq.Eq
import Lemma.Tensor.SEqTS.of.SEq
import Lemma.Tensor.SEqUnsqueezeS.of.SEq.Eq
open Bool Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (A : Tensor α [m, k])
  (B : Tensor α [k, n]) :
-- imply
  let A' : Tensor α [m, 1, k] := A.unsqueeze 1
  let A' : Tensor α [m, n, k] := cast (congrArg (Tensor α) (by simp)) (A'.repeat ⟨1, by grind⟩ n)
  let B' : Tensor α [n, k] := Bᵀ
  let B' : Tensor α [1, n, k] := B'.unsqueeze 0
  let B' : Tensor α [m, n, k] := cast (congrArg (Tensor α) (by simp)) (B'.repeat ⟨0, by grind⟩ m)
  A @ B = (A' * B').sum 2 := by
-- proof
  rw [Dot.eq.Bmm]
  simp [Tensor.bmm]
  congr 1


@[main]
private lemma resize
  [Mul α] [Add α] [Zero α]
-- given
  (A : Tensor α [m, k])
  (B : Tensor α [k', n]) :
-- imply
  let k := k ⊔ k'
  let A' : Tensor α [m, k] := A.resize ⟨1, by grind⟩ k
  let A' : Tensor α [m, 1, k] := A'.unsqueeze 1
  let A' : Tensor α [m, n, k] := cast (congrArg (Tensor α) (by simp)) (A'.repeat ⟨1, by grind⟩ n)
  let B' : Tensor α [k, n] := B.resize ⟨0, by grind⟩ k
  let B' : Tensor α [n, k] := B'ᵀ
  let B' : Tensor α [1, n, k] := B'.unsqueeze 0
  let B' : Tensor α [m, n, k] := cast (congrArg (Tensor α) (by simp)) (B'.repeat ⟨0, by grind⟩ m)
  A @ B = (A' * B').sum 2 := by
-- proof
  simp [Dot.dot]
  unfold einsum
  simp
  apply EqCast.of.SEq.Eq (by simp [broadcast_shape, matmul_shape])
  unfold tensordot
  simp
  unfold matmul bmm
  simp
  apply SEqCast.of.SEq.Eq (by simp [broadcast_shape])
  apply SEqSumS.of.SEq.Eq (by simp [broadcast_shape])
  apply SEqMulS.of.SEq.SEq
  ·
    apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp)
    apply SEqRepeatS.of.SEq.Val.Eq (by simp) (by simp [broadcast_shape])
    apply SEqCast.of.SEq.Eq (by simp [broadcast_shape])
    apply SEqUnsqueezeS.of.SEq.Eq _ (by simp [broadcast_shape])
    apply SEqCast.of.SEq.Eq (by simp [broadcast_shape])
    apply SEqResizeS.of.SEq.Val.Eq (by grind) (by grind)
    rfl
  ·
    apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp)
    apply SEqRepeatS.of.SEq.Val.Eq (by simp) (by simp [broadcast_shape])
    apply SEqCast.of.SEq.Eq (by simp [broadcast_shape])
    apply SEqUnsqueezeS.of.SEq.Eq _ (by simp [broadcast_shape])
    apply SEqCast.of.SEq.Eq (by simp [broadcast_shape])
    apply SEqTS.of.SEq
    apply SEqCast.of.SEq.Eq (by simp [broadcast_shape])
    apply SEqResizeS.of.SEq.Val.Eq (by grind) (by grind)
    rfl


-- created on 2026-07-10
-- updated on 2026-08-13
