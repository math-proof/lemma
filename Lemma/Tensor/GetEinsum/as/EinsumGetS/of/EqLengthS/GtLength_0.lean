import Lemma.Tensor.SEqTensordotS.of.SEq.SEq.Eq.Eq
import Lemma.Bool.SEq.is.Eq
import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.Tensor.Einsum.as.Tensordot.of.EqGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.EqGetS.of.Eq.GtLength_0
import Lemma.Tensor.GetTensordot.as.TensordotGetS.of.EqLengthS.GtLength_0
import Lemma.Tensor.GtLengthEinsum.of.GeLengthS.GeLength_2
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.Tensordot.eq.Matmul.of.EqLengthS
open Bool List Tensor
set_option maxHeartbeats 4000000


@[main, fin, cast, cast.fin]
private lemma main
  [Mul α] [Add α] [Zero α]
  {s s' : List ℕ}
-- given
  (h_s : s.length > 0)
  (h_len : s.length = s'.length)
  (X : Tensor α (s ++ [m, k]))
  (Y : Tensor α (s' ++ [k, n]))
  (i : Fin (s[0] ⊓ s'[0])) :
-- imply
  have h_X : s ++ [m, k] = (s[0] :: s.tail) ++ [m, k] := by
    simpa using congrArg (· ++ [m, k]) (EqCons_Tail.of.GtLength_0 h_s).symm
  have h_Y : s' ++ [k, n] = (s'[0] :: s'.tail) ++ [k, n] := by
    simpa using congrArg (· ++ [k, n]) (EqCons_Tail.of.GtLength_0 (h_len ▸ h_s)).symm
  let X' := cast (congrArg (Tensor α) h_X) X
  let Y' := cast (congrArg (Tensor α) h_Y) Y
  have : i < s[0] := by grind
  have : i < s'[0] := by grind
  (X.einsum Y)[i]'(GtLengthEinsum.of.GeLengthS.GeLength_2 (by grind) (by grind) X Y ⟨i, by grind⟩) ≃ X'[i].einsum Y'[i] := by
-- proof
  intros h_X h_Y X' Y'
  simp only [GetElem.getElem]
  have h_cast := Einsum.eq.Cast_Tensordot.of.EqGetS_SubLength.GeLength_2.GeLength_2 (by grind) (by grind) (by simp) X Y
  erw [EqGetS.of.Eq.GtLength_0 (by simp [matmul_shape]) h_cast ⟨i, by simp [matmul_shape, broadcast_shape]; grind⟩]
  erw [Einsum.eq.Cast_Tensordot.of.EqGetS_SubLength.GeLength_2.GeLength_2 (by grind) (by grind) (by simp) (X'.get ⟨i, by grind⟩) (Y'.get ⟨i, by grind⟩)]
  rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin (by simp [matmul_shape, broadcast_shape]) (by simp [matmul_shape, broadcast_shape])]
  apply SEqCastS.of.SEq.Eq.Eq (by simp [matmul_shape, broadcast_shape]) (by simp [matmul_shape, broadcast_shape])
  simp
  erw [GetTensordot.eq.Cast_TensordotGetS.of.EqLengthS.GtLength_0.fin (i := ⟨i, by grind⟩) (by grind) (by grind)]
  simp
  apply SEqCast.of.SEq.Eq
  .
    simp [broadcast_shape]
    split_ifs <;>
    .
      simp
      grind
  .
    simp [X', Y']
    erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩) (by grind) (by grind)]
    apply Tensor.SEqTensordotS.of.SEq.SEq.Eq.Eq (by grind) (by grind)
    .
      apply SEqCastS.of.SEq.Eq.Eq (by grind) (by grind)
      erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩) (by grind) (by grind)]
      apply SEqCast.of.SEq.Eq (by grind)
      erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin (i := ⟨i, by grind⟩) (by grind) (by grind)]
      apply SEq_Cast.of.SEq.Eq (by grind)
      rfl
    .
      erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩) (by grind) (by grind)]
      apply SEqCastS.of.SEq.Eq.Eq (by grind) (by grind)
      erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩) (by grind) (by grind)]
      apply SEqCast.of.SEq.Eq (by grind)
      erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩) (by grind) (by grind)]
      apply SEqCast.of.SEq.Eq (by grind)
      erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩) (by grind) (by grind)]
      apply SEq_Cast.of.SEq.Eq (by grind)
      rfl


-- created on 2026-07-20
