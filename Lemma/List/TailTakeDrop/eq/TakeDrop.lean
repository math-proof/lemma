import Lemma.List.DropTakeDrop.eq.TakeDrop
open List


@[main, comm]
private lemma main
-- given
  (s : List α)
  (i j : ℕ) :
-- imply
  ((s.drop j).take (i + 1)).tail = (s.drop (j + 1)).take i := by
-- proof
  simp [TakeDrop.eq.DropTakeDrop]


-- created on 2025-10-27
