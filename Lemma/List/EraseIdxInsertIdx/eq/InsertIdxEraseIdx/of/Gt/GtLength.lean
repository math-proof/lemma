import Lemma.List.DropInsertIdx.eq.InsertIdxDrop.of.Ge
import Lemma.List.EqInsertIdx.of.LtLength
import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.InsertIdxAppend.eq.Append_InsertIdx.of.LeLength
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.GtLength
import Lemma.List.TakeInsertIdx.eq.Take.of.Ge
import Lemma.Nat.Add
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.Sub_Add.eq.SubSub
open List Nat


@[main]
private lemma main
  {d : ℕ}
  {s : List α}
-- given
  (h_d : s.length > d)
  (h : k > d)
  (a : α) :
-- imply
  (s.insertIdx k a).eraseIdx d = (s.eraseIdx d).insertIdx (k - 1) a := by
-- proof
  if h_k : s.length ≥ k then
    repeat rw [EraseIdx.eq.Append_Drop_Add_1]
    rw [InsertIdxAppend.eq.Append_InsertIdx.of.LeLength (by simp; omega)]
    simp
    rw [EqMin.of.Le (by omega)]
    rw [TakeInsertIdx.eq.Take.of.Ge (by simp; omega)]
    simp
    rw [DropInsertIdx.eq.InsertIdxDrop.of.Ge (by omega) (by omega)]
    rw [SubSub.eq.Sub_Add]
    rw [Add.comm]
  else
    repeat rw [EqInsertIdx.of.LtLength]
    ·
      rw [LengthEraseIdx.eq.SubLength_1.of.GtLength h_d]
      omega
    ·
      omega


-- created on 2025-11-26
