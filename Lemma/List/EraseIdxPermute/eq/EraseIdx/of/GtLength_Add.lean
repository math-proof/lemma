import Lemma.List.DropTake.eq.TakeDrop
import Lemma.List.EraseIdxAppend.eq.AppendEraseIdx.of.Lt_Length
import Lemma.List.EraseIdxAppend.eq.Append_EraseIdx.of.Ge_Length
import Lemma.List.EraseIdxRotate.eq.Append_EraseIdxTake.of.LeLength_Add.Le_Length
import Lemma.List.Permute.eq.Append_AppendRotateTakeDrop
import Lemma.List.TakeDrop.eq.DropTake
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.EqSubAdd
open List Nat


@[main]
private lemma main
  {s : List ℕ}
  {i d : ℕ}
-- given
  (h : s.length > i + d) :
-- imply
  (s.permute ⟨i, by grind⟩ d).eraseIdx (i + d) = s.eraseIdx i := by
-- proof
  rw [Permute.eq.Append_AppendRotateTakeDrop]
  rw [EraseIdxAppend.eq.Append_EraseIdx.of.Ge_Length (by simp)]
  simp
  rw [EqMin.of.Le (by omega)]
  rw [EqSubAdd.left]
  rw [EraseIdxAppend.eq.AppendEraseIdx.of.Lt_Length]
  ·
    rw [EraseIdxRotate.eq.Append_EraseIdxTake.of.LeLength_Add.Le_Length]
    ·
      simp
      rw [EqMin.of.Le (by omega)]
      simp
      rw [TakeTake.eq.Take.of.Ge (by omega)]
      simp [TakeDrop.eq.DropTake]
      rw [DropTake.eq.TakeDrop]
      rw [Add_Add.eq.AddAdd]
      rw [AddAdd.comm]
      simp
      grind
    ·
      simp
      omega
    ·
      simp
  ·
    simp
    grind


-- created on 2025-10-31
