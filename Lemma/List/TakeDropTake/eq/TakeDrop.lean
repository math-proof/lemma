import Lemma.List.TakeDrop.eq.DropTake
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.List.DropTake.eq.TakeDrop
import Lemma.Nat.AddAdd.eq.Add_Add
open List Nat


@[main, comm]
private lemma main
-- given
  (s : List α)
  (i d j : ℕ) :
-- imply
  ((s.take (i + d + j)).drop i).take d = (s.drop i).take d := by
-- proof
  rw [AddAdd.eq.Add_Add]
  rw [TakeDrop.eq.DropTake]
  rw [TakeTake.eq.Take.of.Ge (by omega)]
  simp [DropTake.eq.TakeDrop]


-- created on 2025-10-25
