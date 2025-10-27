import Lemma.List.DropTake.eq.TakeDrop
import Lemma.List.TakeDrop.eq.DropTake
import Lemma.Nat.Add
import Lemma.Nat.AddAdd.eq.Add_Add
open List Nat


@[main, comm]
private lemma main
-- given
  (s : List α)
  (i d j : ℕ) :
-- imply
  ((s.drop j).take (i + d)).drop d = (s.take (i + j + d)).drop (j + d) := by
-- proof
  rw [TakeDrop.eq.DropTake]
  simp
  apply congrArg
  rw [Add_Add.eq.AddAdd]
  rw [Add.comm (a := j)]


-- created on 2025-10-27
