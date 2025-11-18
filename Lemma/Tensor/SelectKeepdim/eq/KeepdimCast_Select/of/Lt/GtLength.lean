import Lemma.Bool.EqCastS.of.SEq.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.EqSetInsertIdxEraseIdx.of.Lt_Length
import Lemma.List.EraseIdxEraseIdx.eq.EraseIdxEraseIdx.of.Lt.GtLength
import Lemma.List.GetEraseIdx.eq.Get.of.Lt.Lt_Length
import Lemma.List.GetEraseIdx.eq.Get_Add_1.of.Le.LtAdd_1Length
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.Lt_Length
import Lemma.List.LengthInsertIdxEraseIdx.eq.Length.of.Lt_Length
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.Ge_1.of.Gt
import Lemma.Tensor.RepeatCast.eq.Cast_Repeat.of.Eq
import Lemma.Tensor.SelectCast.eq.Cast_Select.of.Eq
import Lemma.Tensor.UnsqueezeCast.eq.CastUnsqueeze.of.Eq
import sympy.tensor.Basic
import sympy.tensor.functions
open Bool List Nat Tensor


@[main, comm]
private lemma main
  [Exp α]
  {s : List ℕ}
  {k : ℕ}
-- given
  (h_s : s.length > d)
  (h_k : k < d)
  (X : Tensor α (s.eraseIdx k))
  (i : Fin s[d]) :
-- imply
  have h_get := GetEraseIdx.eq.Get_Add_1.of.Le.LtAdd_1Length (s := s) (j := d - 1) (i := k) (by omega) (by omega)
  have h_eraseIdx := EraseIdxEraseIdx.eq.EraseIdxEraseIdx.of.Lt.GtLength (s := s) (i := k) (j := d) (by omega) (by omega)
  have h_d_length : d - 1 < (s.eraseIdx k).length := by
    rw [LengthEraseIdx.eq.SubLength_1.of.Lt_Length (by omega)]
    omega
  have h_i_get : ↑i < (s.eraseIdx k)[d - 1] := by
    simp [h_get, EqAddSub.of.Ge (Ge_1.of.Gt h_k)]
  X.keepdim.select ⟨d, h_s⟩ i = (cast (congrArg (Tensor α) h_eraseIdx) (X.select ⟨d - 1, h_d_length⟩ ⟨i, h_i_get⟩)).keepdim := by
-- proof
  intro h_get h_eraseIdx h_d_length h_i_get
  unfold Tensor.keepdim
  simp
  split_ifs with h_k_length h_k_length'
  have h_s : (((s.eraseIdx k).insertIdx k 1).set k (s[k] * ((s.eraseIdx k).insertIdx k 1)[k]'(by grind))) = s := by
    simp [EqSetInsertIdxEraseIdx.of.Lt_Length]
  have h_length := LengthInsertIdxEraseIdx.eq.Length.of.Lt_Length h_k_length 1
  have := SelectCast.eq.Cast_Select.of.Eq (i := ⟨i, by grind⟩) (d := ⟨d, by grind⟩) h_s (X := ((X.unsqueeze k).repeat s[k] ⟨k, by simpa [h_length]⟩))
  simp at this
  rw [this]
  apply EqCastS.of.SEq.Eq
  ·
    simp [EqSetInsertIdxEraseIdx.of.Lt_Length]
  ·
    rw [GetEraseIdx.eq.Get.of.Lt.Lt_Length (by omega) (by omega)]
    rw [UnsqueezeCast.eq.CastUnsqueeze.of.Eq h_eraseIdx]
    have h_s : (((s.eraseIdx k).eraseIdx (d - 1)).insertIdx k 1) = (((s.eraseIdx d).eraseIdx k).insertIdx k 1) := by
      rw [h_eraseIdx]
    rw [RepeatCast.eq.Cast_Repeat.of.Eq h_s ((X.select ⟨d - 1, h_d_length⟩ ⟨i, h_i_get⟩).unsqueeze k) s[k] ⟨k, by grind⟩]
    apply SEq_Cast.of.SEq.Eq
    .
      sorry
    .
      sorry
  repeat grind


-- created on 2025-11-17
