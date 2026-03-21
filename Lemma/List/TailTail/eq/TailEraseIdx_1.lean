import Lemma.List.TailEraseIdx.eq.Drop_2
import Lemma.List.TailTail.eq.Drop_2
open List


@[main]
private lemma main
-- given
  (s : List α) :
-- imply
  s.tail.tail = (s.eraseIdx 1).tail := by
-- proof
  rw [TailEraseIdx.eq.Drop_2]
  apply TailTail.eq.Drop_2


-- created on 2026-01-13
