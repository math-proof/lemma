import Lemma.List.ProdDrop.gt.Zero.of.GtProd_0
open List


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : s.prod > 0) :
-- imply
  s.tail.prod > 0 := by
-- proof
  have := ProdDrop.gt.Zero.of.GtProd_0 h 1
  simp_all


-- created on 2026-04-08
