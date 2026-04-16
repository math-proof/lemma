import Lemma.List.DropLast.eq.Take_SubLength_1
import Lemma.List.TailRotate.eq.Take.of.GtLength_0
open List


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h : s.length > 0) :
-- imply
  (s.rotate (s.length - 1)).tail = s.dropLast := by
-- proof
  rw [TailRotate.eq.Take.of.GtLength_0 h]
  rw [DropLast.eq.Take_SubLength_1]


-- created on 2026-04-16
