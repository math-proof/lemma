import Lemma.List.TakeDrop.eq.DropTake
import Lemma.Nat.EqAddSub.of.Ge
open List Nat


@[main]
private lemma main
-- given
  (h : i ≥ j)
  (s : List α) :
-- imply
  (s.drop (i - j)).take j = (s.take i).drop (i - j) := by
-- proof
  rw [TakeDrop.eq.DropTake]
  rw [EqAddSub.of.Ge h]


-- created on 2025-11-16
