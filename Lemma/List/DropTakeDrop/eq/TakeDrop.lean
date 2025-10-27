import Lemma.List.DropTake.eq.TakeDrop
import Lemma.List.DropTakeDrop.eq.DropTake
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.EqSubAdd
open List Nat


@[main, comm]
private lemma main
-- given
  (s : List α)
  (i d j : ℕ) :
-- imply
  ((s.drop j).take (i + d)).drop d = (s.drop (j + d)).take i := by
-- proof
  rw [DropTakeDrop.eq.DropTake]
  rw [DropTake.eq.TakeDrop]
  rw [AddAdd.eq.Add_Add]
  rw [EqSubAdd]


-- created on 2025-10-27
