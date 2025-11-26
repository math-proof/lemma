import Lemma.List.Lt_LengthInsertIdxEraseIdx.of.GtLength
import Lemma.List.Set.eq.AppendTake__Cons_Drop.of.GtLength
import Lemma.List.TakeInsertIdx.eq.Take.of.Ge
import Lemma.List.TakeEraseIdx.eq.Take.of.Ge
import Lemma.List.DropInsertIdx.eq.Drop.of.Lt
import Lemma.List.DropEraseIdx.eq.Drop.of.Le
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.GtLength
import Lemma.Nat.Le_Sub_1.of.Lt
open List Nat


@[main]
private lemma main
  {dim : ℕ}
  {s : List α}
-- given
  (h : s.length > dim)
  (a : α):
-- imply
  ((s.eraseIdx dim).insertIdx dim a).set dim s[dim] = s := by
-- proof
  rw [Set.eq.AppendTake__Cons_Drop.of.GtLength]
  .
    rw [TakeInsertIdx.eq.Take.of.Ge (by simp)]
    rw [TakeEraseIdx.eq.Take.of.Ge (by simp)]
    simp only [GetElem.getElem]
    rw [DropInsertIdx.eq.Drop.of.Lt (by simp)]
    rw [DropEraseIdx.eq.Drop.of.Le (by rfl)]
    simp
  .
    apply Lt_LengthInsertIdxEraseIdx.of.GtLength h

-- created on 2025-10-04
