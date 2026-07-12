import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.EqSwap_0'1
import Lemma.List.InsertIdxAppend.eq.Append_Cons
import Lemma.List.InsertIdxAppend.eq.Append_InsertIdx
import Lemma.List.SwapAppend.eq.Append_Swap.of.LeLength.LeLength
import Lemma.Tensor.Matmul.as.Bmm.of.Eq
import Lemma.Tensor.Matmul.as.ReshapeMatmul.of.EqGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.SEqMulS.of.SEq.SEq
import Lemma.Tensor.SEqRepeatS.of.SEq.EqValS.Eq
import Lemma.Tensor.SEqSumS.of.SEq.Eq
import Lemma.Tensor.SEqTS.of.SEq
import Lemma.Tensor.SEqUnsqueezeS.of.SEq.Eq
open Bool List Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (A : Tensor α (bz ++ [m, k]))
  (B : Tensor α (bz ++ [k, n])) :
-- imply
  let A' : Tensor α (bz ++ [m, 1, k]) := cast (congrArg (Tensor α) (by simp [InsertIdxAppend.eq.Append_InsertIdx])) (A.unsqueeze (bz.length + 1))
  let A' : Tensor α (bz ++ [m, n, k]) := cast (congrArg (Tensor α) (by simp)) (A'.repeat ⟨bz.length + 1, by grind⟩ n)
  let B' : Tensor α (bz ++ [n, k]) := cast (congrArg (Tensor α) (by rw [SwapAppend.eq.Append_Swap.of.LeLength.LeLength (by simp) (by simp)]; simp [EqSwap_0'1])) Bᵀ
  let B' : Tensor α (bz ++ [1, n, k]) := cast (congrArg (Tensor α) (by simp [InsertIdxAppend.eq.Append_Cons])) (B'.unsqueeze bz.length)
  let B' : Tensor α (bz ++ [m, n, k]) := cast (congrArg (Tensor α) (by simp)) (B'.repeat ⟨bz.length, by grind⟩ m)
  A @ B ≃ (A' * B').sum (bz.length + 2) := by
-- proof
  simp [Dot.dot]
  rw [Matmul.eq.Cast_ReshapeMatmul.of.EqGetS_SubLength.GeLength_2.GeLength_2 (by grind) (by grind) (by grind)]
  apply SEqCast.of.SEq.Eq (by simp [broadcast_shape, matmul_shape])
  simp [tensordot]
  rw [Matmul.eq.Cast_Bmm.of.Eq (by simp)]
  simp
  unfold bmm
  simp
  apply SEqCast.of.SEq.Eq (by simp [broadcast_shape]; grind)
  apply SEqSumS.of.SEq.Eq (by simp)
  apply SEqMulS.of.SEq.SEq
  ·
    apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp)
    apply SEqRepeatS.of.SEq.EqValS.Eq
    ·
      simp
    ·
      simp
    ·
      apply SEqCastS.of.SEq.Eq.Eq
      repeat simp [InsertIdxAppend.eq.Append_InsertIdx]
      apply SEqUnsqueezeS.of.SEq.Eq _ (by grind)
      apply SEqCast.of.SEq.Eq (by simp)
      rfl
  ·
    apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp)
    apply SEqRepeatS.of.SEq.EqValS.Eq
    ·
      simp
    ·
      simp
    ·
      apply SEqCastS.of.SEq.Eq.Eq
      repeat simp [InsertIdxAppend.eq.Append_Cons]
      apply SEqUnsqueezeS.of.SEq.Eq _ (by grind)
      apply SEqCastS.of.SEq.Eq.Eq
      repeat rw [SwapAppend.eq.Append_Swap.of.LeLength.LeLength (by grind) (by grind)]; simp [EqSwap_0'1]
      apply SEqTS.of.SEq
      apply SEqCast.of.Eq
      simp


-- created on 2026-07-10
