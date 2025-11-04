import Lemma.List.Tail.eq.AppendTailTake__Drop.of.Gt_0
import Lemma.List.TailTake.eq.TakeTail
import Lemma.Nat.EqAddSub.of.Ge
open List Nat


@[main]
private lemma main
  {d : ℕ}
-- given
  (s : List α)
  (h : d > 0) :
-- imply
  s.tail = s.tail.take (d - 1) ++ s.drop d := by
-- proof
  have := Tail.eq.AppendTailTake__Drop.of.Gt_0 s h
  apply this.trans
  congr
  rw [← TailTake.eq.TakeTail]
  rwa [EqAddSub.of.Ge]


-- created on 2025-07-06
