import Lemma.List.EqDropAppend.of.Eq_Length
import Lemma.List.Permute__Neg.eq.Append_AppendRotateDropTake
import Lemma.Nat.EqMin.of.Lt
import stdlib.List
open List Nat


@[main, comm]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length)
  (d : ℕ) :
-- imply
  (s.permute i (-d)).drop (i + 1) = s.drop (i + 1) := by
-- proof
  rw [Permute__Neg.eq.Append_AppendRotateDropTake.simp]
  rw [EqDropAppend.of.Eq_Length]
  simp
  grind


-- created on 2025-10-27
