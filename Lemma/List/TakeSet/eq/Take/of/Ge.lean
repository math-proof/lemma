import Lemma.List.EqSet.of.LeLength
import Lemma.List.Set.eq.AppendTake__Cons_Drop.of.Lt_Length
import Lemma.List.TakeAppend.eq.Take.of.GeLength
import Lemma.List.TakeTake.eq.Take.of.Ge
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h : i ≥ j)
  (a : α) :
-- imply
  (s.set i a).take j = s.take j := by
-- proof
  if h_i : i < s.length then
    rw [Set.eq.AppendTake__Cons_Drop.of.Lt_Length h_i]
    rw [TakeAppend.eq.Take.of.GeLength (by simp; omega)]
    apply TakeTake.eq.Take.of.Ge h
  else
    rw [EqSet.of.LeLength]
    omega


-- created on 2025-11-22
