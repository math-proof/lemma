import Lemma.List.DropRotate.eq.Take.of.EqLength_Add
import Lemma.List.Tail.eq.Drop_1
import stdlib.List
open List


@[main, comm]
private lemma main
  {s : List α}
  -- given
  (h : s.length > 0) :
-- imply
  (s.rotate (s.length - 1)).tail = s.take (s.length - 1) := by
-- proof
  rw [Tail.eq.Drop_1]
  rw [DropRotate.eq.Take.of.EqLength_Add]
  omega


-- created on 2025-10-26
