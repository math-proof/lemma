import Lemma.List.DropInsertIdx.eq.Drop.of.Lt
import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.InsertIdxAppend.eq.AppendInsertIdx.of.GeLength
import Lemma.List.TakeInsertIdx.eq.InsertIdxTake.of.Lt.GeLength
import Lemma.Nat.EqAddSub.of.Ge
open List Nat


@[main]
private lemma main
  {d : ℕ}
  {s : List α}
-- given
  (h_k : s.length ≥ k)
  (h : k < d)
  (a : α) :
-- imply
  (s.insertIdx k a).eraseIdx d = (s.eraseIdx (d - 1)).insertIdx k a := by
-- proof
  repeat rw [EraseIdx.eq.Append_Drop_Add_1]
  rw [InsertIdxAppend.eq.AppendInsertIdx.of.GeLength (by simp; omega)]
  rw [DropInsertIdx.eq.Drop.of.Lt (by omega)]
  rw [EqAddSub.of.Ge (by omega)]
  simp
  rw [TakeInsertIdx.eq.InsertIdxTake.of.Lt.GeLength h_k h]


-- created on 2025-11-26
-- updated on 2025-11-27
