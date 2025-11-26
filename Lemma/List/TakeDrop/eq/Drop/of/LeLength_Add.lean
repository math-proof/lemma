import Lemma.List.TakeDrop.eq.DropTake
import Lemma.List.EqTake.of.LeLength
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length ≤ i + j) :
-- imply
  (s.drop i).take j = s.drop i := by
-- proof
  rw [TakeDrop.eq.DropTake]
  rw [EqTake.of.LeLength h]


-- created on 2025-10-23
