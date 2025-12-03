import Lemma.List.DropTake.eq.TakeDrop
import Lemma.List.TakeDropTake.eq.TakeDrop
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqSub_Sub.of.Ge
open List Nat


@[main, comm]
private lemma main
-- given
  (h : i ≥ d)
  (s : List α)
  (j : ℕ) :
-- imply
  ((s.take (i + j)).drop (i - d)).take d = (s.take i).drop (i - d) := by
-- proof
  have := TakeDropTake.eq.TakeDrop s (i - d) d j
  rw [EqAddSub.of.Ge h] at this
  rw [this]
  rw [DropTake.eq.TakeDrop]
  rw [EqSub_Sub.of.Ge h]


-- created on 2025-12-03
