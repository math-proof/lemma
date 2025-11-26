import Lemma.Bool.EqCastS.of.SEq.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.EqGetInsertIdx.of.GeLength
import Lemma.List.EqSetInsertIdxEraseIdx.of.Lt_Length
import Lemma.List.EraseIdxEraseIdx.of.Le.GtLength
import Lemma.List.EraseIdxSet.eq.SetEraseIdx.of.Gt
import Lemma.List.GetEraseIdx.eq.Get.of.Lt.GtLength
import Lemma.List.GetInsertIdx.eq.Get.of.Gt.GeLength
import Lemma.List.GetSet.eq.Get.of.Gt.Lt_Length
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.Lt_Length
import Lemma.List.LengthInsertIdx.eq.Add1Length.of.GeLength
import Lemma.List.LengthInsertIdxEraseIdx.eq.Length.of.Lt_Length
import Lemma.List.LengthSet.eq.Length
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Tensor.RepeatCast.eq.Cast_Repeat.of.Eq
import Lemma.Tensor.SEqRepeatS.of.SEq
import Lemma.Tensor.SelectCast.eq.Cast_Select.of.Eq
import Lemma.Tensor.SelectRepeat.eq.Cast_RepeatSelect.of.Lt_MulGet.Gt.GtLength
import Lemma.Tensor.SelectUnsqueeze.as.UnsqueezeSelect.of.Gt.GeLength
import Lemma.Tensor.UnsqueezeCast.eq.CastUnsqueeze.of.Eq
import sympy.tensor.functions
open Bool List Nat Tensor


@[main, comm]
private lemma main
  {s : List ℕ}
  {k : ℕ}
-- given
  (h_s : s.length > k)
  (h_k : k > d)
  (X : Tensor α (s.eraseIdx k))
  (i : Fin s[d]) :
-- imply
  have h_eraseIdx := EraseIdxEraseIdx.of.Le.GtLength (s := s) (i := d) (j := k - 1) (by omega) (by omega)
  have h_eraseIdx := EqAddSub.of.Ge (show k ≥ 1 by omega) ▸ h_eraseIdx.symm
  X.keepdim.select ⟨d, by omega⟩ i = (cast (congrArg (Tensor α) h_eraseIdx) (X.select ⟨d, by grind⟩ ⟨i, by grind⟩)).keepdim := by
-- proof
  intro h_eraseIdx h_eraseIdx
  unfold Tensor.keepdim
  simp
  split_ifs with h_k_length h_k_length'
  have h_set : (((s.eraseIdx k).insertIdx k 1).set k (s[k] * ((s.eraseIdx k).insertIdx k 1)[k]'(by grind))) = s := by 
    simp [EqSetInsertIdxEraseIdx.of.Lt_Length]
  have h_length := LengthInsertIdxEraseIdx.eq.Length.of.Lt_Length h_k_length 1
  have h_i_lt : i < ((s.eraseIdx k).insertIdx k 1)[d] := by 
    rw [GetInsertIdx.eq.Get.of.Gt.GeLength _ h_k]
    repeat grind
  have := SelectCast.eq.Cast_Select.of.Eq (i := ⟨i, by simp; rwa [GetSet.eq.Get.of.Gt.Lt_Length (by omega) (by omega)]⟩) (d := ⟨d, by rw [LengthSet.eq.Length]; omega⟩) h_set (X := ((X.unsqueeze k).repeat s[k] ⟨k, by simpa [h_length]⟩))
  simp at this
  rw [this]
  apply EqCastS.of.SEq.Eq
  ·
    simp [EqSetInsertIdxEraseIdx.of.Lt_Length]
  ·
    rw [GetEraseIdx.eq.Get.of.Lt.GtLength (by omega) (by omega)]
    rw [UnsqueezeCast.eq.CastUnsqueeze.of.Eq h_eraseIdx]
    have h_insertIdx : (((s.eraseIdx k).eraseIdx d).insertIdx (k - 1) 1) = (((s.eraseIdx d).eraseIdx (k - 1)).insertIdx (k - 1) 1) := by 
      rw [h_eraseIdx]
    have k_le : k - 1 ≤ ((s.eraseIdx k).eraseIdx d).length := by 
      repeat rw [LengthEraseIdx.eq.SubLength_1.of.Lt_Length (by grind)]
      omega
    rw [RepeatCast.eq.Cast_Repeat.of.Eq h_insertIdx ((X.select ⟨d, by grind⟩ ⟨i, by grind⟩).unsqueeze (k - 1)) s[k] ⟨k - 1, by rw [LengthInsertIdx.eq.Add1Length.of.GeLength (by omega)]; omega⟩]
    apply SEq_Cast.of.SEq.Eq
    ·
      simp [h_eraseIdx]
    ·
      rw [SelectRepeat.eq.Cast_RepeatSelect.of.Lt_MulGet.Gt.GtLength _ h_k]
      apply SEqCast.of.SEq.Eq
      ·
        simp
        rw [EraseIdxSet.eq.SetEraseIdx.of.Gt (by omega)]
        rw [GetEraseIdx.eq.Get.of.Lt.GtLength (by omega) (by omega)]
        rw [EqGetInsertIdx.of.GeLength (by grind)]
        simp
      ·
        apply SEqRepeatS.of.SEq
        have := SelectUnsqueeze.as.UnsqueezeSelect.of.Gt.GeLength (by grind) h_k X ⟨i, by grind⟩
        simp at this
        assumption
  repeat grind


-- created on 2025-11-26
