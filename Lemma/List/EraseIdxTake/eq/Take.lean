import Lemma.List.TakeEraseIdx.eq.EraseIdxTake.of.Le
import Lemma.List.TakeEraseIdx.eq.Take.of.Ge
open List


@[main]
private lemma main
-- given
  (s : List α) :
-- imply
  (s.take (i + 1)).eraseIdx i = s.take i := by
-- proof
  rw [← TakeEraseIdx.eq.EraseIdxTake.of.Le (by rfl)]
  simp [TakeEraseIdx.eq.Take.of.Ge (by rfl)]


-- created on 2025-11-28
