import Lemma.List.TakeCons.eq.Cons_Take
import Lemma.Nat.EqAddSub.of.Ge
open List Nat


@[main]
private lemma main
-- given
  (h : i > 0)
  (a : α)
  (b : List α) :
-- imply
  (a :: b).take i = a :: b.take (i - 1) := by
-- proof
  rw [← TakeCons.eq.Cons_Take]
  rw [EqAddSub.of.Ge]
  omega


-- created on 2025-11-18
