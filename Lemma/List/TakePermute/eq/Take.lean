import Lemma.List.Permute.eq.Append_AppendRotateTakeDrop
import Lemma.List.EqTakeAppend.of.Eq_Length
import Lemma.List.LengthTake.eq.Min_Length
import Lemma.Nat.EqMin.of.Lt
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length)
  (d : ℕ) :
-- imply
  (s.permute i d).take i = s.take i := by
-- proof
  rw [Permute.eq.Append_AppendRotateTakeDrop]
  rw [EqTakeAppend.of.Eq_Length]
  rw [LengthTake.eq.Min_Length]
  apply EqMin.of.Lt
  simp


-- created on 2025-10-12
