import Lemma.List.EqCons_Tail.of.GtLength_0
open List


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h : s.length > 0)
  (h_a : a = s[0]) :
-- imply
  a :: s.tail = s :=
-- proof
  h_a ▸ EqCons_Tail.of.GtLength_0 h


-- created on 2025-10-07
