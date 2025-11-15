import Lemma.List.TailRotate.eq.Take.of.GtLength_0
import stdlib.List
open List


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h : s.length = n + 1) :
-- imply
  (s.rotate n).tail = s.take n := by
-- proof
  have := TailRotate.eq.Take.of.GtLength_0 (s := s) (by omega)
  simp_all


-- created on 2025-10-31
