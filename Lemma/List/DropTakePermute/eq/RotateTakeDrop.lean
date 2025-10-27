import Lemma.List.TakeDrop.eq.DropTake
import Lemma.List.TakeDropPermute.eq.RotateTakeDrop
open List


@[main, comm]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length)
  (d : ℕ) :
-- imply
  ((s.permute i d).take (i + d + 1)).drop i = ((s.drop i).take (d + 1)).rotate 1 := by
-- proof
  rw [← TakeDropPermute.eq.RotateTakeDrop]
  rw [TakeDrop.eq.DropTake]
  grind


-- created on 2025-10-15
-- updated on 2025-10-27
