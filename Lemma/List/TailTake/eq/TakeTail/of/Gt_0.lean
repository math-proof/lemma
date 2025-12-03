import Lemma.List.TailTake.eq.TakeTail
import Lemma.Nat.EqAddSub.of.Ge
open List Nat


@[main]
private lemma main
-- given
  (h : i > 0)
  (s : List α) :
-- imply
  (s.take i).tail = s.tail.take (i - 1) := by
-- proof
  have := TailTake.eq.TakeTail s (i - 1)
  rwa [EqAddSub.of.Ge (by omega)] at this


-- created on 2025-12-03
