import Lemma.List.TailTake.eq.TakeTail
import Lemma.Nat.EqAddSub.of.Ge
open List Nat


@[main]
private lemma main
-- given
  (s : List α)
  (h : i > 0) :
-- imply
  s.tail.take (i - 1) = (s.take i).tail := by
-- proof
  have := TailTake.eq.TakeTail s (i - 1)
  rw [EqAddSub.of.Ge (by omega)] at this
  aesop


-- created on 2025-11-04
