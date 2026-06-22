import Lemma.Tensor.SEqSelectS.of.SEq
import Lemma.Tensor.GetSelect.as.SelectGet.of.Lt_Get_0.Lt_Get_Add_1.LtAdd_1Length
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.Cons_Append_List.eq.AppendTake_Length
import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.Nat.EqAddMulDiv
import Lemma.Tensor.BroadcastMatmul.as.BroadcastMatmulRec
import Lemma.Tensor.EqGet0_0
import Lemma.Tensor.EqGetS.of.Eq.GtLength_0
import Lemma.Tensor.GetAppend.as.AppendCastS_Get.of.GtLength_0
import Lemma.Tensor.GetBroadcastMatmul.as.BroadcastMatmulRecGet.of.GtLength_0
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetDot.eq.DotGet.of.Lt
import Lemma.Tensor.GetRepeat.as.RepeatGet.of.Lt_Get_0.GtLength_0
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
import Lemma.Tensor.Matmul.as.BroadcastMatmul.of.LtGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.Matmul.as.SelectBatchDot.of.LtGet_SubLength_1.GeLength_2
import Lemma.Tensor.SEq0S.of.Eq
import Lemma.Tensor.SEqAppendS.of.SEq.SEq.EqLengthS
import Lemma.Tensor.SEqBroadcastMatmulRecS.of.SEq.SEq.Eq.Eq
import Lemma.Tensor.SEqBroadcastS.of.Eq.Eq
import Lemma.Tensor.SEqRepeatS.of.SEq
open Tensor Bool List Nat
set_option maxHeartbeats 20000000


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h : k < n')
  (X : Tensor α (n :: (s ++ [k])))
  (Y : Tensor α [n', k'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by simp) (by apply GeLength_1.of.Ne_Nil (by simp)) X Y i) ≃ X[i] @ Y := by
-- proof
  simp [GetElem.getElem]
  match s with
  | [] =>
    rw [GetDot.eq.DotGet.of.Lt.fin h]
  | s₀ :: s =>
    have h_min_length : s.length ⊓ (s.length + 1 + 1) = s.length := by omega
    simp [MatMul.dot]
    have := Matmul.eq.Cast_BroadcastMatmul.of.LtGetS_SubLength.GeLength_2.GeLength_2 (by simp) (by simp) (by simpa) X Y
    rw [EqGetS.of.Eq.GtLength_0 (by simp [matmul_shape]) this ⟨i, by simp [matmul_shape, broadcast_shape]⟩]
    conv_rhs => rw [Matmul.eq.Cast_BroadcastMatmul.of.LtGetS_SubLength.GeLength_2.GeLength_2 (by simp) (by simp) (by simpa)]
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
          rw [EqAddMulDiv]
          apply Cons_Append_List.eq.AppendTake_Length
        ·
          rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩)]
          ·
            apply SEqCast.of.SEq.Eq
            ·
              simp
              rw [EqAddMulDiv]
              apply Cons_Append_List.eq.AppendTake_Length
            ·
              simp
              rw [GetAppend.eq.Cast_AppendCastS_Get.of.GtLength_0.fin (by simp) _ _ ⟨i, by simp⟩]
              simp [@Tensor.EqGet0_0.fin]
              apply SEqCast.of.SEq.Eq (by simp)
              apply SEqAppendS.of.SEq.SEq.EqLengthS
              ·
                simp
              ·
                apply SEqCastS.of.SEq.Eq.Eq
                ·
                  simp
                ·
                  simp [h_min_length]
                  apply AppendTake_Length.eq.Cons_Append_List
                ·
                  rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩)]
                  ·
                    apply SEqCast.of.SEq.Eq
                    ·
                      simp [h_min_length]
                      apply AppendTake_Length.eq.Cons_Append_List
                    ·
                      simp
                      rw [GetRepeat.eq.Cast_RepeatGet.of.Lt_Get_0.GtLength_0.fin (by simp) (by grind) _ _ ⟨(s ++ [k]).length, by simp; grind⟩]
                      apply SEqCast.of.SEq.Eq (by simp)
                      apply SEqRepeatS.of.SEq (d := ⟨(s ++ [k]).length, by simp; grind⟩)
                      rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩)]
                      ·
                        apply SEqCastS.of.SEq.Eq.Eq
                        repeat {
                          simp
                          apply Cons_Append_List.eq.AppendTake_Length
                        }
                        ·
                          simp
                          rfl
                      ·
                        simp
                        apply Cons_Append_List.eq.AppendTake_Length
                      ·
                        simp
                  ·
                    simp [h_min_length]
                    apply AppendTake_Length.eq.Cons_Append_List
                  ·
                    simp
              ·
                apply SEqCast.of.SEq.Eq (by simp)
                apply SEq0S.of.Eq
                simp
          ·
            simp
            rw [EqAddMulDiv]
            apply Cons_Append_List.eq.AppendTake_Length
          ·
            simp
      ·
        apply SEqBroadcastS.of.Eq.Eq
        ·
          simp
        ·
          rfl


@[main, fin]
private lemma one
  [NonUnitalNonAssocSemiring α]
-- given
  (h : k < n')
  (X : Tensor α (n :: (s ++ [k])))
  (Y : Tensor α [n'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by simp) (by simp) X Y i) ≃ X[i] @ Y := by
-- proof
  simp [GetElem.getElem]
  match s with
  | [] =>
    rw [GetDot.eq.DotGet.of.Lt.one.fin h]
  | s₀ :: s =>
    simp [MatMul.dot]
    rw [Matmul.eq.Cast_SelectBatchDot.of.LtGet_SubLength_1.GeLength_2 (by simp) (by simpa)]
    conv_rhs => rw [Matmul.eq.Cast_SelectBatchDot.of.LtGet_SubLength_1.GeLength_2 (by simp) (by simpa)]
    simp
    apply SEq_Cast.of.SEq.Eq
    ·
      simp [matmul_shape]
      simp [EraseIdx.eq.Append_Drop_Add_1, AppendTake_Length.eq.Cons_Append_List]
    ·
      conv_lhs => rw [show i = ⟨i, by simp⟩ by grind]
      rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin]
      .
        apply SEqCast.of.SEq.Eq
        .
          simp [AppendTake_Length.eq.Cons_Append_List]
          simp [matmul_shape]
          grind
        .
          rw [GetSelect.eq.Cast_SelectGet.of.Lt_Get_0.Lt_Get_Add_1.LtAdd_1Length]
          .
            apply SEqCast.of.SEq.Eq
            .
              simp [EraseIdx.eq.Append_Drop_Add_1, AppendTake_Length.eq.Cons_Append_List]
            .
              apply SEqSelectS.of.SEq
              -- have h_bz : (n :: s₀ :: (s ++ [k])).take ((s ++ [k]).length + 1 + 1 - 2) = n :: (s₀ :: (s ++ [k])).take s.length := by
              --   simp
              -- have h_nk : [(n :: s₀ :: (s ++ [k]))[(s ++ [k]).length + 1 + 1 - 2], n'] = [(s₀ :: (s ++ [k]))[s.length], n'] := by
              --   simp
              -- have h_s₀ : (n :: s₀ :: (s ++ [k])).take ((s ++ [k]).length + 1 + 1 - 2) = n :: (s₀ :: (s ++ [k])).take s.length := by
              --   simp
              -- have h_s₀' : ((s₀ :: (s ++ [k])).take ((s ++ [k]).length + 1 - 2) ++ [n', 1]) = (s₀ :: (s ++ [k])).take s.length ++ [n', 1] := by
              --   simp
              -- sorry
              simp [Tensor.batch_dot]
              apply SEq_Cast.of.SEq.Eq
              .
                simp [AppendTake_Length.eq.Cons_Append_List]
                rw [EqMin.of.Lt (by omega)]
                rw [EraseIdxAppend.eq.Append_EraseIdx.of.LeLength (by grind)]
                simp
                rw [EqMin.of.Lt (by omega)]
                simp [AppendTake_Length.eq.Cons_Append_List]
              .
                sorry
          .
            simp [AppendTake_Length.eq.Cons_Append_List]
          .
            simp [AppendTake_Length.eq.Cons_Append_List]
            apply i.isLt
      .
        simp [matmul_shape]
      .
        simp [matmul_shape]
        simp [EraseIdx.eq.Append_Drop_Add_1, AppendTake_Length.eq.Cons_Append_List]


-- created on 2026-01-11
-- updated on 2026-01-13
