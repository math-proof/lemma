import Lemma.List.EqCons_Tail.of.GtLength_0
open List


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h : s.length > i) :
-- imply
  s[0] :: s.tail = s := by
-- proof
  apply EqCons_Tail.of.GtLength_0


-- created on 2026-07-20
