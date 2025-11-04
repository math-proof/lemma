import Lemma.List.TailEraseIdx.eq.Drop_2
import Lemma.List.TailTake.eq.TakeTail
open List


@[main]
private lemma main
-- given
  (s : List α)
  (i : ℕ) :
-- imply
  ((s.eraseIdx 1).take (i + 1)).tail = (s.drop 2).take i := by
-- proof
  rw [TailTake.eq.TakeTail]
  rw [TailEraseIdx.eq.Drop_2]


-- created on 2025-11-04
