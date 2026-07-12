import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.Cons_Append_List.eq.AppendTake_Length
import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.Tensor.Tensordot.as.Matmul
import Lemma.Tensor.EqGetS.of.Eq.GtLength_0
import Lemma.Tensor.GetBmm.as.BmmGetS.of.Eq
import Lemma.Tensor.GetReshape.as.Reshape.of.EqProdS.GtLength_0
import Lemma.Tensor.GetTensordot.as.MatmulGet.of.GtLength_0
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetDot.eq.DotGet.of.Ge
import Lemma.Tensor.GetSelect.as.SelectGet.of.Lt_Get_0.Lt_Get_Add_1.LtAdd_1Length
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
import Lemma.Tensor.Einsum.as.Tensordot.of.GeGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.Einsum.as.SelectBmm.of.EqGet_SubLength_1.GeLength_2
import Lemma.Tensor.Einsum.as.SelectBmm.of.GtGet_SubLength_1.GeLength_2
import Lemma.Tensor.SEqBmmS.of.SEq.SEq
import Lemma.Tensor.SEqMatmulS.of.SEq.SEq.Eq.Eq
import Lemma.Tensor.SEqReshapeS.of.Eq.Eq.Dvd
import Lemma.Tensor.SEqSelectS.of.SEq
open Bool List Tensor
set_option maxHeartbeats 1000000


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h : k ≥ n')
  (X : Tensor α (n :: (s ++ [k])))
  (Y : Tensor α [n', k'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by simp) (by apply GeLength_1.of.Ne_Nil (by simp)) X Y i) ≃ X[i] @ Y := by
-- proof
  simp [GetElem.getElem]
  match s with
  | [] =>
    rw [GetDot.eq.DotGet.of.Ge.fin h]
  | s₀ :: s =>
    have h_min_length : s.length ⊓ (s.length + 1 + 1) = s.length := by omega
    simp [Dot.dot]
    have := Matmul.eq.Cast_Tensordot.of.GeGetS_SubLength.GeLength_2.GeLength_2 (by simp) (by simp) (by simpa) X Y
    rw [EqGetS.of.Eq.GtLength_0 (by simp [matmul_shape]) this ⟨i, by simp [matmul_shape, broadcast_shape]⟩]
    conv_rhs => rw [Matmul.eq.Cast_Tensordot.of.GeGetS_SubLength.GeLength_2.GeLength_2 (by simp) (by simp) (by simpa)]
    apply SEq_Cast.of.SEq.Eq (by simp [matmul_shape, broadcast_shape])
    simp
    rw [GetTensordot.eq.Cast_MatmulGet.of.GtLength_0.fin (by simp) _ _ ⟨i, by simp⟩]
    simp [Tensordot.eq.Cast_Matmul]
    apply SEqCastS.of.SEq.Eq.Eq
    ·
      simp [matmul_shape, broadcast_shape]
    ·
      simp [broadcast_shape]
      split_ifs
      repeat simp_all
    ·
      apply SEqMatmulS.of.SEq.SEq.Eq.Eq
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
        apply SEqReshapeS.of.Eq.Eq.Dvd
        ·
          simp
        ·
          rfl


@[main, fin]
private lemma une
  [Mul α] [AddCommMonoid α]
-- given
  (h : k ≥ n')
  (X : Tensor α (n :: (s ++ [k])))
  (Y : Tensor α [n'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by simp) (by simp) X Y i) ≃ X[i] @ Y := by
-- proof
  simp [GetElem.getElem]
  match s with
  | [] =>
    rw [GetDot.eq.DotGet.of.Ge.une.fin h]
  | s₀ :: s =>
    simp [Dot.dot]
    if h_gt : k > n' then
      rw [Matmul.eq.Cast_SelectBmm.of.GtGet_SubLength_1.GeLength_2 (by simp) (by simpa using h_gt)]
      conv_rhs => rw [Matmul.eq.Cast_SelectBmm.of.GtGet_SubLength_1.GeLength_2 (by simp) (by simpa using h_gt)]
      simp
      apply SEq_Cast.of.SEq.Eq
      ·
        simp [matmul_shape]
        simp [EraseIdx.eq.Append_Drop_Add_1, AppendTake_Length.eq.Cons_Append_List]
      ·
        conv_lhs => rw [show i = ⟨i, by simp⟩ by grind]
        rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin]
        ·
          apply SEqCast.of.SEq.Eq
          ·
            simp [AppendTake_Length.eq.Cons_Append_List]
            simp [matmul_shape]
            grind
          ·
            rw [GetSelect.eq.Cast_SelectGet.of.Lt_Get_0.Lt_Get_Add_1.LtAdd_1Length]
            ·
              apply SEqCast.of.SEq.Eq
              ·
                simp [EraseIdx.eq.Append_Drop_Add_1, AppendTake_Length.eq.Cons_Append_List]
              ·
                apply SEqSelectS.of.SEq
                have h_bz : (n :: s₀ :: (s ++ [k])).take ((s ++ [k]).length + 1 + 1 - 2) = n :: (s₀ :: (s ++ [k])).take s.length := by
                  simp
                rw [GetBmm.eq.Cast_BmmGetS.of.Eq.fin h_bz]
                apply SEqCast.of.SEq.Eq
                ·
                  simp [AppendTake_Length.eq.Cons_Append_List]
                ·
                  apply SEqBmmS.of.SEq.SEq
                  ·
                    apply SEq_Cast.of.SEq.Eq
                    ·
                      simp [AppendTake_Length.eq.Cons_Append_List]
                    ·
                      rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin]
                      apply SEqCast.of.SEq.Eq (by simp)
                      rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩)]
                      ·
                        apply SEqCast.of.SEq.Eq
                        ·
                          simp [AppendTake_Length.eq.Cons_Append_List]
                        ·
                          simp
                          rfl
                      ·
                        simp [AppendTake_Length.eq.Cons_Append_List]
                      ·
                        simp
                      ·
                        simp
                      ·
                        simp
                  ·
                    rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin]
                    apply SEqCast.of.SEq.Eq (by simp)
                    rw [GetBroadcast.eq.Cast_Broadcast.of.EqProdS.GtLength_0.fin (by grind) (by grind) _ ⟨i, by grind⟩]
                    apply SEqCast.of.SEq.Eq (by simp)
                    apply SEqReshapeS.of.Eq.Eq.Dvd
                    repeat simp
            ·
              simp [AppendTake_Length.eq.Cons_Append_List]
            ·
              simp [AppendTake_Length.eq.Cons_Append_List]
              apply i.isLt
        ·
          simp [matmul_shape]
        ·
          simp [matmul_shape]
          simp [EraseIdx.eq.Append_Drop_Add_1, AppendTake_Length.eq.Cons_Append_List]
    else
      have hk : k = n' := by omega
      subst hk
      rw [Matmul.eq.Cast_SelectBmm.of.EqGet_SubLength_1.GeLength_2 (by simp) (by simp)]
      conv_rhs => rw [Matmul.eq.Cast_SelectBmm.of.EqGet_SubLength_1.GeLength_2 (by simp) (by simp)]
      simp
      apply SEq_Cast.of.SEq.Eq
      ·
        simp [matmul_shape]
        simp [EraseIdx.eq.Append_Drop_Add_1, AppendTake_Length.eq.Cons_Append_List]
      ·
        conv_lhs => rw [show i = ⟨i, by simp⟩ by grind]
        rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin]
        ·
          apply SEqCast.of.SEq.Eq
          ·
            simp [AppendTake_Length.eq.Cons_Append_List]
            simp [matmul_shape]
            grind
          ·
            rw [GetSelect.eq.Cast_SelectGet.of.Lt_Get_0.Lt_Get_Add_1.LtAdd_1Length]
            ·
              apply SEqCast.of.SEq.Eq
              ·
                simp [EraseIdx.eq.Append_Drop_Add_1, AppendTake_Length.eq.Cons_Append_List]
              ·
                apply SEqSelectS.of.SEq
                have h_bz : (n :: s₀ :: (s ++ [k])).take ((s ++ [k]).length + 1 + 1 - 2) = n :: (s₀ :: (s ++ [k])).take s.length := by
                  simp
                rw [GetBmm.eq.Cast_BmmGetS.of.Eq.fin h_bz]
                apply SEqCast.of.SEq.Eq
                ·
                  simp [AppendTake_Length.eq.Cons_Append_List]
                ·
                  apply SEqBmmS.of.SEq.SEq
                  ·
                    apply SEq_Cast.of.SEq.Eq
                    ·
                      simp [AppendTake_Length.eq.Cons_Append_List]
                    ·
                      rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin]
                      apply SEqCast.of.SEq.Eq (by simp)
                      rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩)]
                      ·
                        apply SEqCast.of.SEq.Eq
                        ·
                          simp [AppendTake_Length.eq.Cons_Append_List]
                        ·
                          simp
                          rfl
                      ·
                        simp [AppendTake_Length.eq.Cons_Append_List]
                      ·
                        simp
                      ·
                        simp
                      ·
                        simp
                  ·
                    rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin]
                    apply SEqCast.of.SEq.Eq (by simp)
                    rw [GetBroadcast.eq.Cast_Broadcast.of.EqProdS.GtLength_0.fin (by grind) (by grind) Y ⟨i, by grind⟩]
                    apply SEqCast.of.SEq.Eq (by simp)
                    apply SEqReshapeS.of.Eq.Eq.Dvd
                    repeat simp
            ·
              simp [AppendTake_Length.eq.Cons_Append_List]
            ·
              simp [AppendTake_Length.eq.Cons_Append_List]
              apply i.isLt
        ·
          simp [matmul_shape]
        ·
          simp [matmul_shape]
          simp [EraseIdx.eq.Append_Drop_Add_1, AppendTake_Length.eq.Cons_Append_List]


-- created on 2026-01-13
-- updated on 2026-07-06
