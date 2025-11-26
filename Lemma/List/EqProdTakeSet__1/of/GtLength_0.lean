import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.List.EqGetSet.of.GtLength
open List


@[main]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (h : s.length > 0)
  (a : α) :
-- imply
  ((s.set 0 a).take 1).prod = a := by
-- proof
  rw [ProdTake_1.eq.Get_0.of.GtLength_0 (by grind)]
  rw [EqGetSet.of.GtLength h]


-- created on 2025-07-18
