import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.Cons_Append_List.eq.AppendTake_Length
import Lemma.Tensor.Einsum.as.Tensordot.of.LtGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.EqGetS.of.Eq.GtLength_0
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetDot.eq.DotGet.of.Lt
import Lemma.Tensor.GetEinsum.as.EinsumGet.of.Lt.GtLengthS
import Lemma.Tensor.GetResize.as.ResizeGet.of.GtGet_0.GtVal_0
import Lemma.Tensor.GetTensordot.as.MatmulGet.of.GtLength_0
import Lemma.Tensor.GtLengthDot.of.GeLengthS
import Lemma.Tensor.SEqMatmulS.of.SEq.SEq.Eq.Eq
import Lemma.Tensor.SEqReshapeS.of.Eq.Eq.Dvd
import Lemma.Tensor.SEqResizeS.of.SEq.EqValS.Eq
import Lemma.Tensor.Tensordot.as.Matmul
open Bool List Tensor
set_option maxHeartbeats 5000000


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s : s.length > s'.length)
  (h : k < n')
  (X : Tensor α (n :: (s ++ [k])))
  (Y : Tensor α (s' ++ [n', k']))
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.GeLengthS (by grind) X Y i) ≃ X[i] @ Y := by
-- proof
  simp [GetElem.getElem]
  match s, s' with
  | [], [] =>
    erw [GetDot.eq.DotGet.of.Lt.fin h]
    rfl
  | sₐ :: sₜ, [] =>
    have h_min_length : sₜ.length ⊓ (sₜ.length + 1 + 1) = sₜ.length := by omega
    simp [Dot.dot]
    have := Einsum.eq.Cast_Tensordot.of.LtGetS_SubLength.GeLength_2.GeLength_2 (by simp) (by simp) (by simpa) X Y
    erw [EqGetS.of.Eq.GtLength_0 (by simp [matmul_shape]) this ⟨i, by simp [matmul_shape, broadcast_shape]⟩]
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
      split_ifs <;> simp_all
    ·
      apply SEqMatmulS.of.SEq.SEq.Eq.Eq (by simp) (by rfl) (by rfl)
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
        apply SEqReshapeS.of.Eq.Eq.Dvd (by simp) (by simp) (by rfl)
  | sₐ :: sₜ, s'ₐ :: s'ₜ =>
    simp [Dot.dot]
    simpa using GetEinsum.as.EinsumGet.of.Lt.GtLengthS (by grind) h X Y i


-- created on 2026-07-16
