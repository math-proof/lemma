import Lemma.List.DropTakePermute.eq.RotateTakeDrop
import Lemma.List.EqTake.of.LeLength
open List


@[main, comm]
private lemma main
  {s : List α}
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : i + d ≥ s.length - 1) :
-- imply
  (s.permute i d).drop i = ((s.drop i).take (d + 1)).rotate 1 := by
-- proof
  rw [RotateTakeDrop.eq.DropTakePermute]
  apply congrArg
  apply Eq_Take.of.LeLength
  simp
  omega


-- created on 2025-10-27
