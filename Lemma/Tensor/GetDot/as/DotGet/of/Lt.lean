import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.Cons_Append_List.eq.AppendTake_Length
import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.List.SetAppend.eq.Append_Set.of.LeLength
import Lemma.Tensor.Einsum.as.SelectBmm.of.LtGet_SubLength_1.GeLength_2
import Lemma.Tensor.Einsum.as.Tensordot.of.LtGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetBmm.as.BmmGetS.of.Eq
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetDot.eq.DotGet.of.Lt
import Lemma.Tensor.GetReshape.as.Reshape.of.EqProdS.GtLength_0
import Lemma.Tensor.GetResize.as.ResizeGet.of.GtGet_0.GtVal_0
import Lemma.Tensor.GetSelect.as.SelectGet.of.GtGet_0.GtGet_Add_1.LtAdd_1Length
import Lemma.Tensor.GetTensordot.as.MatmulGet.of.GtLength_0
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
import Lemma.Tensor.SEqBmmS.of.SEq.SEq
import Lemma.Tensor.SEqMatmulS.of.SEq.SEq.Eq.Eq
import Lemma.Tensor.SEqReshapeS.of.Eq.Eq.Dvd
import Lemma.Tensor.SEqResizeS.of.SEq.EqValS.Eq
import Lemma.Tensor.SEqSelectS.of.SEq
import Lemma.Tensor.Tensordot.as.Matmul
open Bool List Tensor
set_option maxHeartbeats 1000000


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
    erw [GetDot.eq.DotGet.of.Lt.fin h]
    rfl
  | s₀ :: s =>
    have h_min_length : s.length ⊓ (s.length + 1 + 1) = s.length := by omega
    simp [Dot.dot]
    have := Einsum.eq.Cast_Tensordot.of.LtGetS_SubLength.GeLength_2.GeLength_2 (by simp) (by simp) (by simpa) X Y
    erw [Get.of.Eq.GtLength_0 (by simp [matmul_shape]) this ⟨i, by simp [matmul_shape, broadcast_shape]⟩]
    conv_rhs => erw [Einsum.eq.Cast_Tensordot.of.LtGetS_SubLength.GeLength_2.GeLength_2 (by simp) (by simp) (by simpa)]
    simp
    apply SEq_Cast.of.SEq.Eq (by simp [matmul_shape, broadcast_shape])
    erw [GetTensordot.eq.Cast_MatmulGet.of.GtLength_0.fin (by simp) _ _ ⟨i, by simp⟩]
    simp [Tensordot.eq.Cast_Matmul]
    apply SEqCastS.of.SEq.Eq.Eq
    ·
      simp [matmul_shape, broadcast_shape]
    ·
      simp [broadcast_shape]
      split_ifs
      repeat simp_all
    ·
      apply SEqMatmulS.of.SEq.SEq.Eq.Eq (by simp) (by rfl) (by rfl)
      apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp)
      rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩) (by simp) (by simp)]
      apply SEqCast.of.SEq.Eq (by simp)
      simp
      rw [GetResize.eq.Cast_ResizeGet.of.GtGet_0.GtVal_0.fin (by simp) (by grind) (d := ⟨((n :: s₀ :: (s ++ [k])).take ((s ++ [k]).length + 1 + 1 - 2)).length + 1, by grind⟩)]
      simp
      apply SEqCast.of.SEq.Eq (by simp)
      apply SEqResizeS.of.SEq.EqValS.Eq (by simp) (by simp)
      have h_cons := Cons_Append_List.eq.AppendTake_Length s s₀ k k
      erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩) (by grind) (by simpa)]
      ·
        simp
        apply SEqCastS.of.SEq.Eq.Eq (by simpa) (by simpa)
        rfl
      ·
        apply SEqReshapeS.of.Eq.Eq.Dvd (by simp) (by simp) (by rfl)


@[main, fin]
private lemma une
  [Mul α] [Add α] [Zero α]
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
    erw [GetDot.eq.DotGet.of.Lt.une.fin h]
    rfl
  | s₀ :: s =>
    simp [Dot.dot]
    rw [Einsum.eq.Cast_SelectBmm.of.LtGet_SubLength_1.GeLength_2 (by simp) (by simpa)]
    conv_rhs => rw [Einsum.eq.Cast_SelectBmm.of.LtGet_SubLength_1.GeLength_2 (by simp) (by simpa)]
    simp
    apply SEq_Cast.of.SEq.Eq
    ·
      simp [matmul_shape]
      simp [EraseIdx.eq.Append_Drop_Add_1, AppendTake_Length.eq.Cons_Append_List]
    ·
      conv_lhs => rw [show i = ⟨i, by simp⟩ by grind]
      erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin]
      ·
        apply SEqCast.of.SEq.Eq
        ·
          simp [AppendTake_Length.eq.Cons_Append_List]
          simp [matmul_shape]
          grind
        ·
          rw [GetSelect.eq.Cast_SelectGet.of.GtGet_0.GtGet_Add_1.LtAdd_1Length]
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
                  apply SEq_Cast.of.SEq.Eq (by simp)
                  ·
                    rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin (by simp) (by simp)]
                    apply SEqCast.of.SEq.Eq (by simp)
                    rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩) (by simp) (by simp)]
                    apply SEqCast.of.SEq.Eq (by simp)
                    rw [GetResize.eq.Cast_ResizeGet.of.GtGet_0.GtVal_0.fin (by simp) (by grind) (d := ⟨((n :: s₀ :: (s ++ [k])).take ((s ++ [k]).length + 1 + 1 - 2)).length + 1, by grind⟩)]
                    apply SEqCast.of.SEq.Eq (by simp)
                    simp
                    apply SEqResizeS.of.SEq.EqValS.Eq (by simp) (by simp)
                    have h_cons := Cons_Append_List.eq.AppendTake_Length s s₀ k k
                    erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩) (by grind) (by simpa)]
                    simp
                    apply SEqCastS.of.SEq.Eq.Eq (by simpa) (by simpa) (by rfl)
                ·
                  rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin]
                  apply SEqCast.of.SEq.Eq (by simp)
                  rw [GetReshape.eq.Cast_Reshape.of.EqProdS.GtLength_0.fin (by grind) (by grind) (i := ⟨i, by grind⟩)]
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


-- created on 2026-01-11
-- updated on 2026-07-15
