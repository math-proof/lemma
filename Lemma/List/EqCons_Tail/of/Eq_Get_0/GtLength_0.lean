import Lemma.List.EqCons_Tail.of.GtLength_0
open List


@[main, comm]
private lemma main
  {v : List α}
-- given
  (h : v.length > 0)
  (h_a : a = v[0]) :
-- imply
  a :: v.tail = v := 
-- proof
  h_a ▸ EqCons_Tail.of.GtLength_0 h


-- created on 2025-10-07
