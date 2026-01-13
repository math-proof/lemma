import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.Tensor.EqGetS.of.Eq.GtLength_0
import Lemma.Tensor.GetDot.as.DotGet.of.Gt
import Lemma.Tensor.GetDot.as.DotGet.of.Lt
import Lemma.Tensor.GetDot.eq.DotGet
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
import Lemma.Tensor.Matmul.eq.Cast_BroadcastMatmul.of.EqGetS_SubLength.GeLength_2.GeLength_2
open List Tensor Bool


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α (n :: (s ++ [k])))
  (Y : Tensor α [n', k'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by simp) (by apply GeLength_1.of.Ne_Nil (by simp)) X Y i) ≃ X[i] @ Y := by
-- proof
  if h_n : k < n' then
    apply GetDot.as.DotGet.of.Lt h_n
  else if h_n : k > n' then
    apply GetDot.as.DotGet.of.Gt h_n
  else
    have h_n : k = n' := by omega
    subst h_n
    simp [GetElem.getElem]
    match s with
    | [] =>
      rw [GetDot.eq.DotGet.fin]
    | s₀ :: s =>
      simp [MatMul.dot]
      have := Matmul.eq.Cast_BroadcastMatmul.of.EqGetS_SubLength.GeLength_2.GeLength_2 (by simp) (by simp) (by simp) X Y
      rw [EqGetS.of.Eq.GtLength_0 (by simp [matmul_shape]) this ⟨i, by simp [matmul_shape, broadcast_shape]⟩]
      rw [Matmul.eq.Cast_BroadcastMatmul.of.EqGetS_SubLength.GeLength_2.GeLength_2 (by simp) (by simp) (by simp)]
      simp
      apply SEq_Cast.of.SEq.Eq (by simp [matmul_shape, broadcast_shape])
      rw [GetBroadcastMatmul.eq.Cast_BroadcastMatmulRecGet.of.GtLength_0.fin (by simp) _ _ ⟨i, by simp⟩]
      simp [BroadcastMatmul.eq.Cast_BroadcastMatmulRec]
      apply SEqCastS.of.SEq.Eq.Eq
      .
        simp [matmul_shape, broadcast_shape]
      .
        simp [broadcast_shape]
        split_ifs
        repeat simp_all
      .
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
