import Lemma.List.TakeDropPermute.eq.RotateTakeDrop.of.GtLength_Add
import Lemma.List.TakeDrop.eq.DropTake
import Lemma.Nat.AddAdd.eq.Add_Add
open List Nat


@[main, comm]
private lemma main
  {s : List α}
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : s.length > i + d) :
-- imply
  ((s.permute i d).take (i + d + 1)).drop i = ((s.drop i).take (d + 1)).rotate 1 := by
-- proof
  rw [← TakeDropPermute.eq.RotateTakeDrop.of.GtLength_Add h]
  rw [TakeDrop.eq.DropTake]
  rw [Add_Add.eq.AddAdd]


-- created on 2025-10-15
-- updated on 2025-10-23
