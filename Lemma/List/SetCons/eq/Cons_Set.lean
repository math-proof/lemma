import Lemma.List.EqSet.of.LeLength
import Lemma.List.Set.eq.AppendTake__Cons_Drop.of.GtLength
open List


@[main, comm]
private lemma main
-- given
  (head : α)
  (tail : List α)
  (i : ℕ)
  (a : α) :
-- imply
  (head :: tail).set (i + 1) a = head :: tail.set i a := by
-- proof
  if h_i : i < tail.length then
    repeat rw [Set.eq.AppendTake__Cons_Drop.of.GtLength (by grind)]
    grind
  else
    repeat rw [EqSet.of.LeLength (by grind)]


-- created on 2026-07-10
