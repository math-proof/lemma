import Lemma.List.Drop.eq.Nil.of.Ge_Length
import Lemma.List.Tail.eq.Drop_1
import stdlib.List
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length ≤ 1) :
-- imply
  s.tail = [] := by
-- proof
  rw [Tail.eq.Drop_1]
  rw [Drop.eq.Nil.of.Ge_Length]
  omega


-- created on 2025-11-04
