import Lemma.Algebra.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.Algebra.EqGetSet.of.Lt_Length
open Algebra


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
  rw [ProdTake_1.eq.Get_0.of.GtLength_0]
  rw [EqGetSet.of.Lt_Length h]


-- created on 2025-07-18
