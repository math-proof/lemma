import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.InsertIdxAppend.eq.Append_InsertIdx.of.LeLength
open List


@[main]
private lemma main
  {d : ℕ}
  {s : List α}
-- given
  (h : k > d)
  (a : α) :
-- imply
  (s.insertIdx k a).eraseIdx d = (s.eraseIdx d).insertIdx (k - 1) a := by
-- proof
  repeat rw [EraseIdx.eq.Append_Drop_Add_1]
  rw [InsertIdxAppend.eq.Append_InsertIdx.of.LeLength (by simp; omega)]
  sorry


-- created on 2025-11-26
