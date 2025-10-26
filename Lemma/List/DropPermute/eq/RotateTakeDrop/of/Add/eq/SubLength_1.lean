import Lemma.List.DropTakePermute.eq.RotateTakeDrop.of.GtLength_Add
import Lemma.List.EqTake.of.Ge_Length
open List


@[main, comm]
private lemma main
  {s : List α}
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : i + d = s.length - 1) :
-- imply
  (s.permute i d).drop i = ((s.drop i).take (d + 1)).rotate 1 := by
-- proof
  rw [← DropTakePermute.eq.RotateTakeDrop.of.GtLength_Add (by omega)]
  apply congrArg
  apply Eq_Take.of.Ge_Length
  simp
  omega


-- created on 2025-10-23
