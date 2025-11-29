import Lemma.List.DropEraseIdx.eq.Drop.of.Le
import Lemma.List.DropInsertIdx.eq.InsertIdxDrop.of.Ge.GeLength
open List


@[main]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (h_d : s.length > d) :
-- imply
  (((s.eraseIdx d).insertIdx d 1).drop d).prod = (s.drop (d + 1)).prod := by
-- proof
  rw [DropInsertIdx.eq.InsertIdxDrop.of.Ge.GeLength (by grind) (by rfl)]
  simp
  rw [DropEraseIdx.eq.Drop.of.Le (by rfl)]


-- created on 2025-11-29
