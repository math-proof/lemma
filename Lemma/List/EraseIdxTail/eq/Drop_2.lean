import Lemma.List.EraseIdx_0.eq.Tail
import Lemma.List.TailTail.eq.Drop_2
import stdlib.Slice
open List


@[main]
private lemma main
  {s : List α} :
-- imply
  s.tail.eraseIdx 0 = s.drop 2 := by
-- proof
  rw [EraseIdx_0.eq.Tail]
  apply TailTail.eq.Drop_2


-- created on 2025-11-03
