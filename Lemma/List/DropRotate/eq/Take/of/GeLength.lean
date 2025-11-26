import stdlib.List
import Lemma.List.Rotate.eq.AppendDrop__Take.of.GeLength
import Lemma.List.EqDropAppend.of.Eq_Length
import Lemma.List.LengthDrop.eq.SubLength
open List


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h : s.length ≥ n) :
-- imply
  (s.rotate n).drop (s.length - n) = s.take n := by
-- proof
  rw [Rotate.eq.AppendDrop__Take.of.GeLength h]
  rw [EqDropAppend.of.Eq_Length]
  apply LengthDrop.eq.SubLength


-- created on 2025-10-20
