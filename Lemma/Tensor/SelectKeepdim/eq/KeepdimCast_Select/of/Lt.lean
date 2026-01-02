import Lemma.Bool.EqCastS.of.SEq.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.EqGetInsertIdx.of.GeLength
import Lemma.List.EqSetInsertIdxEraseIdx.of.GtLength
import Lemma.List.EraseIdxEraseIdx.of.Gt.GtLength
import Lemma.List.EraseIdxSet.eq.SetEraseIdx.of.Lt
import Lemma.List.GetEraseIdx.eq.Get.of.Gt.GtLength
import Lemma.List.GetEraseIdx.eq.Get_Add_1.of.Le.LtAdd_1Length
import Lemma.List.GetInsertIdx.eq.Get.of.Lt.GeLength
import Lemma.List.GetSet.eq.Get.of.Lt.GtLength
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.GtLength
import Lemma.List.LengthInsertIdx.eq.Add1Length.of.GeLength
import Lemma.List.LengthInsertIdxEraseIdx.eq.Length.of.GtLength
import Lemma.List.LengthSet.eq.Length
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.Ge_1.of.Gt
import Lemma.Tensor.RepeatCast.eq.Cast_Repeat.of.Eq
import Lemma.Tensor.SEqRepeatS.of.SEq
import Lemma.Tensor.SEqSelectS.of.SEq.EqValS.EqValS
import Lemma.Tensor.SelectCast.eq.Cast_Select.of.Eq
import Lemma.Tensor.SelectRepeat.eq.Cast_RepeatSelect.of.Lt
import Lemma.Tensor.SelectUnsqueeze.as.UnsqueezeSelect.of.Le
import Lemma.Tensor.UnsqueezeCast.eq.CastUnsqueeze.of.Eq
import sympy.tensor.functions
open Bool List Nat Tensor


@[main, comm]
private lemma main
  {s : List ℕ}
  {d : Fin s.length}
  {k : ℕ}
-- given
  (h_k : k < d)
  (X : Tensor α (s.eraseIdx k))
  (i : Fin s[d]) :
-- imply
  have h_get := GetEraseIdx.eq.Get_Add_1.of.Le.LtAdd_1Length (s := s) (j := d - 1) (i := k) (by omega) (by omega)
  have h_eraseIdx := (EraseIdxEraseIdx.of.Gt.GtLength (s := s) (i := d) (j := k) (by omega) h_k).symm
  have h_d_length : d - 1 < (s.eraseIdx k).length := by
    rw [LengthEraseIdx.eq.SubLength_1.of.GtLength (by omega)]
    omega
  have h_i_get : ↑i < (s.eraseIdx k)[d.val - 1] := by
    simp [h_get, EqAddSub.of.Ge (Ge_1.of.Gt h_k)]
  X.keepdim.select d i = (cast (congrArg (Tensor α) h_eraseIdx) (X.select ⟨d - 1, h_d_length⟩ ⟨i, h_i_get⟩)).keepdim := by
-- proof
  intro h_get h_eraseIdx h_d_length h_i_get
  unfold Tensor.keepdim
  simp
  split_ifs with h_k_length h_k_length'
  have h_set : (((s.eraseIdx k).insertIdx k 1).set k (s[k] * ((s.eraseIdx k).insertIdx k 1)[k]'(by grind))) = s := by
    simp [EqSetInsertIdxEraseIdx.of.GtLength]
  have h_length := LengthInsertIdxEraseIdx.eq.Length.of.GtLength h_k_length 1
  have h_i_lt : i < ((s.eraseIdx k).insertIdx k 1)[d] := by
    simp [GetInsertIdx.eq.Get.of.Lt.GeLength (by omega) h_k (s := s.eraseIdx k) 1]
    omega
  have := SelectCast.eq.Cast_Select.of.Eq (i := ⟨i, by simp; rwa [GetSet.eq.Get.of.Lt.GtLength (by omega) (by omega)]⟩) (d := ⟨d, by rw [LengthSet.eq.Length]; omega⟩) h_set (X := ((X.unsqueeze k).repeat s[k] ⟨k, by simpa [h_length]⟩))
  simp at this
  rw [this]
  apply EqCastS.of.SEq.Eq
  ·
    simp [EqSetInsertIdxEraseIdx.of.GtLength]
  ·
    rw [GetEraseIdx.eq.Get.of.Gt.GtLength (by omega) (by omega)]
    rw [UnsqueezeCast.eq.CastUnsqueeze.of.Eq h_eraseIdx]
    have h_insertIdx : (((s.eraseIdx k).eraseIdx (d - 1)).insertIdx k 1) = (((s.eraseIdx d).eraseIdx k).insertIdx k 1) := by
      rw [h_eraseIdx]
    have k_le : k ≤ ((s.eraseIdx k).eraseIdx (d - 1)).length := by
      rw [LengthEraseIdx.eq.SubLength_1.of.GtLength (by omega)]
      omega
    rw [RepeatCast.eq.Cast_Repeat.of.Eq h_insertIdx ((X.select ⟨d - 1, h_d_length⟩ ⟨i, h_i_get⟩).unsqueeze k) s[k] ⟨k, by rw [LengthInsertIdx.eq.Add1Length.of.GeLength (by omega)]; omega⟩]
    apply SEq_Cast.of.SEq.Eq
    ·
      simp [h_eraseIdx]
    ·
      rw [SelectRepeat.eq.Cast_RepeatSelect.of.Lt (by simpa) (X.unsqueeze k) (d := ⟨d, by grind⟩) ⟨i, by simp; grind⟩]
      apply SEqCast.of.SEq.Eq
      ·
        simp
        rw [EraseIdxSet.eq.SetEraseIdx.of.Lt (by omega)]
        rw [GetEraseIdx.eq.Get.of.Gt.GtLength (by omega) (by omega)]
        rw [EqGetInsertIdx.of.GeLength (by omega)]
        simp
      ·
        apply SEqRepeatS.of.SEq
        have := SelectUnsqueeze.as.UnsqueezeSelect.of.Le (by simp; omega) X ⟨i, by omega⟩ (k := k) (d := ⟨d - 1, by omega⟩)
        simp at this
        symm
        apply this.symm.trans
        apply SEqSelectS.of.SEq.EqValS.EqValS
        .
          rfl
        .
          simp
          omega
        .
          rfl
  repeat grind


-- created on 2025-11-17
-- updated on 2025-11-29
