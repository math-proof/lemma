import Lemma.List.Rotate.eq.AppendDrop__Take.of.GeLength
import Lemma.List.EqTakeAppend.of.Eq_Length
import Lemma.List.LengthDrop.eq.SubLength
open List


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h : s.length ≥ n) :
-- imply
  (s.rotate n).take (s.length - n) = s.drop (n) := by
-- proof
  rw [Rotate.eq.AppendDrop__Take.of.GeLength h]
  rw [EqTakeAppend.of.Eq_Length]
  apply LengthDrop.eq.SubLength


-- created on 2025-10-20
