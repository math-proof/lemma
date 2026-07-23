import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.AppendAppend.eq.Append_Append
import Lemma.List.Cons_Append_List.eq.AppendTake_Length
import Lemma.List.DropCons.eq.Drop_Sub_1.of.Gt_0
import Lemma.List.TailAppend.eq.AppendTail.of.GtLength_0
import Lemma.List.TakeAppend.eq.Take.of.GeLength
import Lemma.List.TakeCons.eq.Cons_Take.of.Gt_0
import Lemma.List.TakeTake.eq.Take.of.Gt
import Lemma.List.ZipWith_Append.eq.AppendZipWithS
import Lemma.List.ZipWith__Append.eq.AppendZipWithS
import Lemma.Tensor.Einsum.as.Tensordot.of.LtGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.EqGetS.of.Eq.GtLength_0
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetResize.as.ResizeGet.of.GtGet_0.GtVal_0
import Lemma.Tensor.GetTensordot.as.MatmulGet.of.GtLengthS
import Lemma.Tensor.GtLengthDot.of.GeLengthS
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.ReshapeCast.eq.Reshape.of.EqProdS.Eq
import Lemma.Tensor.SEqMatmulS.of.SEq.SEq.Eq.Eq
import Lemma.Tensor.SEqReshape.of.Eq
import Lemma.Tensor.SEqReshapeS.of.Eq.Eq.Dvd
import Lemma.Tensor.SEqResizeS.of.SEq.EqValS.Eq
import Lemma.Tensor.Tensordot.as.Matmul.of.GtLengthS
import Lemma.Tensor.Tensordot.as.Matmul.of.LtLengthS
import Lemma.Tensor.Tensordot.eq.Matmul.of.EqLengthS
open Bool List Tensor
set_option maxHeartbeats 1000000


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s : sₜ.length > s'ₜ.length)
  (h : k < n')
  (X : Tensor α (n :: (sₐ :: sₜ ++ [k])))
  (Y : Tensor α (s'ₐ :: s'ₜ ++ [n', k']))
  (i : Fin n) :
-- imply
  (X.einsum Y)[i]'(GtLengthDot.of.GeLengthS (by grind) X Y i) ≃ X[i].einsum Y := by
-- proof
  simp [GetElem.getElem]
  have h_batch : (n :: sₐ :: sₜ).length > (s'ₐ :: s'ₜ).length := by
    simp only [List.length_cons]
    have h_tail : sₜ.length ≥ s'ₜ.length := by omega
    omega
  have h_min_length : sₜ.length ⊓ (sₜ.length + 1 + 1) = sₜ.length := by omega
  have := Einsum.eq.Cast_Tensordot.of.LtGetS_SubLength.GeLength_2.GeLength_2 (by simp) (by simp) (by simpa) X Y
  erw [EqGetS.of.Eq.GtLength_0 (by simp [matmul_shape]) this ⟨i, by
    rw [← Length.eq.Get_0.of.GtLength_0 (by simp [matmul_shape])]
    exact GtLengthDot.of.GeLengthS (by grind) X Y i⟩]
  conv_rhs => erw [Einsum.eq.Cast_Tensordot.of.LtGetS_SubLength.GeLength_2.GeLength_2 (by simp) (by simp) (by simpa)]
  simp
  apply SEq_Cast.of.SEq.Eq (by simp [matmul_shape, broadcast_shape])
  rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by simp [broadcast_shape]; split_ifs; repeat grind⟩) (by simp) (by simp [broadcast_shape, matmul_shape])]
  apply SEqCast.of.SEq.Eq (by simp [broadcast_shape, matmul_shape])
  simp
  if h_s : sₜ.length > s'ₜ.length + 1 then
    erw [GetTensordot.eq.Cast_MatmulGet.of.GtLengthS.fin (by simp; grind) _ _ ⟨i, by simp⟩]
    apply SEqCast.of.SEq.Eq
    ·
      simp [broadcast_shape]
      split_ifs with h h h h h h h h
      ·
        omega
      ·
        omega
      ·
        omega
      ·
        omega
      ·
        omega
      ·
        omega
      ·
        omega
      ·
        simp [h_min_length]
        rw [TailAppend.eq.AppendTail.of.GtLength_0 (by grind)]
        rw [Append_Append.eq.AppendAppend]
        congr 1
        repeat rw [TakeCons.eq.Cons_Take.of.Gt_0 (by grind)]
        repeat rw [TakeTake.eq.Take.of.Gt (by grind)]
        simp
        repeat rw [TakeAppend.eq.Take.of.GeLength (by grind)]
        rw [Take.eq.TakeTake.of.Gt (i := sₜ.length - 1) (j := sₜ.length - (s'ₜ.length + 1) - 1) (by grind)]
        rw [ZipWith__Append.eq.AppendZipWithS]
        rw [TakeTake.eq.Take.of.Gt (by grind)]
        simp
        congr 1
        congr 1
        repeat rw [DropCons.eq.Drop_Sub_1.of.Gt_0 (by grind)]
        congr 1
      ·
        omega
    ·
      rw [Tensordot.eq.Cast_Matmul.of.GtLengthS]
      apply SEq_Cast.of.SEq.Eq
      ·
        simp [broadcast_shape]
        split_ifs with h h h h h h h h
        ·
          omega
        ·
          omega
        ·
          omega
        ·
          omega
        ·
          omega
        ·
          omega
        ·
          omega
        ·
          simp [h_min_length]
          rw [Append_Append.eq.AppendAppend]
          repeat rw [TakeCons.eq.Cons_Take.of.Gt_0 (by grind)]
          repeat rw [TakeTake.eq.Take.of.Gt (by grind)]
          simp
          repeat rw [TakeAppend.eq.Take.of.GeLength (by grind)]
          rw [Take.eq.TakeTake.of.Gt (i := sₜ.length - 1) (j := sₜ.length - (s'ₜ.length + 1) - 1) (by grind)]
          rw [ZipWith__Append.eq.AppendZipWithS]
          rw [TakeTake.eq.Take.of.Gt (by grind)]
          simp
          congr 1
          rw [DropCons.eq.Drop_Sub_1.of.Gt_0 (by grind)]
        ·
          simp
          omega
      ·
        apply SEqMatmulS.of.SEq.SEq.Eq.Eq (by simp) (by rfl) (by simp; grind)
        apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp)
        rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩) (by simp) (by simp)]
        apply SEqCast.of.SEq.Eq (by simp)
        simp
        rw [GetResize.eq.Cast_ResizeGet.of.GtGet_0.GtVal_0.fin (by simp) (by grind)]
        simp
        apply SEqCast.of.SEq.Eq (by simp)
        apply SEqResizeS.of.SEq.EqValS.Eq (by simp) (by simp)
        have h_cons := Cons_Append_List.eq.AppendTake_Length sₜ sₐ k k
        erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩) (by grind) (by simpa)]
        ·
          simp
          apply SEqCastS.of.SEq.Eq.Eq (by simpa) (by simpa)
          rfl
        ·
          apply SEqReshapeS.of.Eq.Eq.Dvd (by simp) (by simp) (by rfl)
      ·
        simp
        grind
  else
    have h_s : sₜ.length = s'ₜ.length + 1 := by omega
    erw [GetTensordot.eq.Cast_MatmulGet.of.GtLengthS.fin (by simp; grind) _ _ ⟨i, by simp⟩]
    apply SEqCast.of.SEq.Eq
    ·
      simp [broadcast_shape]
      split_ifs with h h h h h h h h
      ·
        omega
      ·
        omega
      ·
        omega
      ·
        omega
      ·
        omega
      ·
        omega
      ·
        omega
      ·
        simp [h_min_length]
        rw [TailAppend.eq.AppendTail.of.GtLength_0 (by grind)]
        rw [Append_Append.eq.AppendAppend]
        repeat rw [TakeCons.eq.Cons_Take.of.Gt_0 (by grind)]
        simp
        repeat rw [TakeAppend.eq.Take.of.GeLength (by grind)]
        conv_rhs =>
          rw [TakeCons.eq.Cons_Take.of.Gt_0 (by grind)]
          rw [DropCons.eq.Drop_Sub_1.of.Gt_0 (by grind)]
        rw [ZipWith__Append.eq.AppendZipWithS]
        simp
        congr 1
      ·
        omega
    ·
      rw [Tensordot.eq.Matmul.of.EqLengthS (by simp [h_s]; omega)]
      apply SEqMatmulS.of.SEq.SEq.Eq.Eq (by simp) (by rfl) (by simp; grind)
      apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp)
      rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩) (by simp) (by simp)]
      apply SEqCast.of.SEq.Eq (by simp)
      simp
      rw [GetResize.eq.Cast_ResizeGet.of.GtGet_0.GtVal_0.fin (by simp) (by grind) (d := ⟨((n :: sₐ :: (sₜ ++ [k])).take ((sₜ ++ [k]).length + 1 + 1 - 2)).length + 1, by grind⟩)]
      simp
      apply SEqCast.of.SEq.Eq (by simp)
      apply SEqResizeS.of.SEq.EqValS.Eq (by simp) (by simp)
      have h_cons := Cons_Append_List.eq.AppendTake_Length sₜ sₐ k k
      erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩) (by grind) (by simpa)]
      ·
        simp
        apply SEqCastS.of.SEq.Eq.Eq (by simpa) (by simpa)
        rfl
      ·
        apply SEq_Cast.of.SEq.Eq (by simp)
        erw [ReshapeCast.eq.Reshape.of.EqProdS.Eq (by simp) (by simp)]
        apply SEqReshape.of.Eq
        congr 1
        ·
          simp
          omega
        ·
          simp


-- created on 2026-07-16
-- updated on 2026-07-17
