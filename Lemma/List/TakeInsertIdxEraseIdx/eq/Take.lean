import Lemma.List.TakeEraseIdx.eq.Take
import Lemma.List.TakeInsertIdx.eq.Take
open List


@[main]
private lemma main
  [Monoid α]
-- given
  (s : List α)
  (a : α := 1) :
-- imply
  ((s.eraseIdx d).insertIdx d a).take d = s.take d := by
-- proof
  rw [TakeInsertIdx.eq.Take]
  rw [TakeEraseIdx.eq.Take]


-- created on 2025-12-04
