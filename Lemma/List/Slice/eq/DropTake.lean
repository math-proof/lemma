import Lemma.List.DropTake.eq.TakeDrop
import stdlib.List
open List


@[main]
private lemma main
-- given
  (s : List α) :
-- imply
  s.slice i j = (s.take j).drop i := by
-- proof
  unfold List.slice List.array_slice
  simp
  rw [← DropTake.eq.TakeDrop]


-- created on 2025-11-28
