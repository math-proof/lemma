import Lemma.List.Append_DropTake.eq.Take
import Lemma.List.TakeDrop.eq.DropTake
import Lemma.Nat.EqAddSub.of.Ge
open List Nat


@[main, comm]
private lemma main
  {i d : ℕ}
-- given
  (h : i ≥ d)
  (s : List α) :
-- imply
  s.take (i - d) ++ (s.drop (i - d)).take d = s.take i := by
-- proof
  rw [TakeDrop.eq.DropTake]
  rw [EqAddSub.of.Ge (by omega)]
  rw [Append_DropTake.eq.Take]


-- created on 2025-11-16
