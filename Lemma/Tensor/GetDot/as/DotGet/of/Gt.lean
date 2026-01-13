import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.Cons_Append_List.eq.AppendTake_Length
import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.Tensor.BroadcastMatmul.eq.Cast_BroadcastMatmulRec
import Lemma.Tensor.EqGetS.of.Eq.GtLength_0
import Lemma.Tensor.GetBroadcastMatmul.eq.Cast_BroadcastMatmulRecGet.of.GtLength_0
import Lemma.Tensor.GetCast.eq.Cast_Get.of.Eq.GtLength_0
import Lemma.Tensor.GetDot.eq.DotGet.of.Gt
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
import Lemma.Tensor.Matmul.eq.Cast_BroadcastMatmul.of.GtGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.SEqBroadcastMatmulRecS.of.SEq.SEq.Eq.Eq
import Lemma.Tensor.SEqBroadcastS.of.Eq.Eq
open Bool List Tensor
set_option maxHeartbeats 2000000


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h : k > n')
  (X : Tensor α (n :: (s ++ [k])))
  (Y : Tensor α [n', k'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by simp) (by apply GeLength_1.of.Ne_Nil (by simp)) X Y i) ≃ X[i] @ Y := by
-- proof
  simp [GetElem.getElem]
  match s with
  | [] =>
    rw [GetDot.eq.DotGet.of.Gt.fin h]
  | s₀ :: s =>
    have h_min_length : s.length ⊓ (s.length + 1 + 1) = s.length := by omega
    simp [MatMul.dot]
    have := Matmul.eq.Cast_BroadcastMatmul.of.GtGetS_SubLength.GeLength_2.GeLength_2 (by simp) (by simp) (by simpa) X Y
    rw [EqGetS.of.Eq.GtLength_0 (by simp [matmul_shape]) this ⟨i, by simp [matmul_shape, broadcast_shape]⟩]
    rw [Matmul.eq.Cast_BroadcastMatmul.of.GtGetS_SubLength.GeLength_2.GeLength_2 (by simp) (by simp) (by simpa)]
    simp
    apply SEq_Cast.of.SEq.Eq (by simp [matmul_shape, broadcast_shape])
    rw [GetBroadcastMatmul.eq.Cast_BroadcastMatmulRecGet.of.GtLength_0.fin (by simp) _ _ ⟨i, by simp⟩]
    simp [BroadcastMatmul.eq.Cast_BroadcastMatmulRec]
    apply SEqCastS.of.SEq.Eq.Eq
    ·
      simp [matmul_shape, broadcast_shape]
    ·
      simp [broadcast_shape]
      split_ifs
      repeat simp_all
    ·
      apply SEqBroadcastMatmulRecS.of.SEq.SEq.Eq.Eq
      ·
        simp
      ·
        rfl
      ·
        rfl
      ·
        apply SEqCastS.of.SEq.Eq.Eq
        ·
          simp
        ·
          simp
          apply Cons_Append_List.eq.AppendTake_Length
        ·
          rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩)]
          ·
            apply SEqCast.of.SEq.Eq
            ·
              simp
              apply Cons_Append_List.eq.AppendTake_Length
            ·
              simp
              rfl
          ·
            simp
            apply Cons_Append_List.eq.AppendTake_Length
          ·
            simp
      ·
        apply SEqBroadcastS.of.Eq.Eq
        ·
          simp
        ·
          rfl


-- created on 2026-01-13
