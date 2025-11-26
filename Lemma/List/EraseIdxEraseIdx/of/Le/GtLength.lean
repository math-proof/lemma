import Lemma.List.DropTake.eq.TakeDrop
import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.EraseIdxAppend.eq.AppendEraseIdx.of.GtLength
import Lemma.List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.Nat.AddAdd
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.EqAdd_Sub.of.Ge
import Lemma.Nat.EqMin.of.Lt
import Lemma.Nat.SubAddS.eq.Sub
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h_i : i < s.length)
  (h₁ : i ≤ j) :
-- imply
  (s.eraseIdx i).eraseIdx j = (s.eraseIdx (j + 1)).eraseIdx i := by
-- proof
  rw [EraseIdx.eq.Append_Drop_Add_1 s i]
  rw [EraseIdxAppend.eq.Append_EraseIdx.of.LeLength]
  ·
    rw [EraseIdx.eq.Append_Drop_Add_1 s (j + 1)]
    rw [EraseIdxAppend.eq.AppendEraseIdx.of.GtLength]
    ·
      rw [EraseIdx.eq.Append_Drop_Add_1 _ i]
      rw [TakeTake.eq.Take.of.Ge (by omega)]
      simp
      rw [EqMin.of.Lt h_i]
      rw [EraseIdx.eq.Append_Drop_Add_1]
      simp
      rw [AddAdd.comm]
      rw [Add_Add.eq.AddAdd]
      rw [EqAdd_Sub.of.Ge (by omega)]
      simp
      rw [DropTake.eq.TakeDrop]
      rw [SubAddS.eq.Sub]
    ·
      simp
      omega
  ·
    simp
    omega


-- created on 2025-11-17
