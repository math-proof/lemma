import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.Cons_Append_List.eq.AppendTake_Length
import Lemma.Tensor.Einsum.as.Tensordot.of.GeGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.EqGetS.of.Eq.GtLength_0
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetDot.eq.DotGet.of.Ge
import Lemma.Tensor.GetEinsum.as.EinsumGet.of.Ge.GtLengthS
import Lemma.Tensor.GetTensordot.as.MatmulGet.of.GtLength_0
import Lemma.Tensor.GtLengthDot.of.GeLengthS
import Lemma.Tensor.SEqMatmulS.of.SEq.SEq.Eq.Eq
import Lemma.Tensor.SEqReshapeS.of.Eq.Eq.Dvd
import Lemma.Tensor.Tensordot.as.Matmul
open Bool List Tensor
set_option maxHeartbeats 5000000


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s : s.length > s'.length)
  (h : k ≥ n')
  (X : Tensor α (n :: (s ++ [k])))
  (Y : Tensor α (s' ++ [n', k']))
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.GeLengthS (by grind) X Y i) ≃ X[i] @ Y := by
-- proof
  simp [GetElem.getElem]
  match s, s' with
  | [], [] =>
    erw [GetDot.eq.DotGet.of.Ge.fin h]
    rfl
  | sₐ :: sₜ, [] =>
    have h_min_length : sₜ.length ⊓ (sₜ.length + 1 + 1) = sₜ.length := by omega
    simp [Dot.dot]
    have := Einsum.eq.Cast_Tensordot.of.GeGetS_SubLength.GeLength_2.GeLength_2 (by simp) (by simp) (by grind) X Y
    erw [EqGetS.of.Eq.GtLength_0 (by simp [matmul_shape]) this ⟨i, by simp [matmul_shape, broadcast_shape]⟩]
    conv_rhs => rw [Einsum.eq.Cast_Tensordot.of.GeGetS_SubLength.GeLength_2.GeLength_2 (by simp) (by simp) (by grind)]
    apply SEq_Cast.of.SEq.Eq (by simp [matmul_shape, broadcast_shape])
    simp
    rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by simp [broadcast_shape]⟩) (by grind) (by simp [broadcast_shape, matmul_shape])]
    apply SEqCast.of.SEq.Eq (by simp [matmul_shape, broadcast_shape])
    erw [GetTensordot.eq.Cast_MatmulGet.of.GtLength_0.fin (by simp) _ _ ⟨i, by simp⟩]
    simp [Tensordot.eq.Cast_Matmul]
    apply SEqCastS.of.SEq.Eq.Eq
    ·
      simp [broadcast_shape]
    ·
      simp [broadcast_shape]
      split_ifs
      repeat simp_all
    ·
      apply SEqMatmulS.of.SEq.SEq.Eq.Eq (by simp) (by rfl) (by rfl)
      ·
        apply SEqCastS.of.SEq.Eq.Eq (by simp)
        ·
          simp
          apply Cons_Append_List.eq.AppendTake_Length
        ·
          erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩)]
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
  | sₐ :: sₜ, s'ₐ :: s'ₜ =>
    simp [Dot.dot]
    simpa using GetEinsum.as.EinsumGet.of.Ge.GtLengthS (by grind) h X Y i


-- created on 2026-07-18
