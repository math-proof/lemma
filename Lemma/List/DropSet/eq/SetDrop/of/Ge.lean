import Lemma.List.DropAppend.eq.AppendDrop.of.GeLength
import Lemma.List.DropTake.eq.TakeDrop
import Lemma.List.EqSet.of.LeLength
import Lemma.List.Set.eq.AppendTake__Cons_Drop.of.GtLength
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.EqAdd_Sub.of.Ge
open List Nat


@[main]
private lemma main
-- given
  (h : i ≥ j)
  (s : List α)
  (a : α) :
-- imply
  (s.set i a).drop j = (s.drop j).set (i - j) a := by
-- proof
  if h_i : i < s.length then
    repeat rw [Set.eq.AppendTake__Cons_Drop.of.GtLength (by grind)]
    rw [DropAppend.eq.AppendDrop.of.GeLength (by grind)]
    simp [← DropTake.eq.TakeDrop]
    rw [Add_Add.eq.AddAdd]
    rw [EqAdd_Sub.of.Ge h]
  else
    rw [EqSet.of.LeLength (by omega)]
    rw [EqSet.of.LeLength]
    grind


-- created on 2025-11-22
