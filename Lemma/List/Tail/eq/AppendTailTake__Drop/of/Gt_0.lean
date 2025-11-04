import Lemma.List.EqAppendTake__Drop
import Lemma.List.TakeTail.eq.TailTake.of.Gt_0
import Lemma.Nat.EqAddSub.of.Ge
open List Nat


@[main]
private lemma main
  {d : ℕ}
-- given
  (s : List α)
  (h : d > 0) :
-- imply
  s.tail = (s.take d).tail ++ s.drop d := by
-- proof
  rw [← EqAppendTake__Drop s.tail (d - 1)]
  simp
  rw [EqAddSub.of.Ge (by assumption)]
  congr
  rwa [TakeTail.eq.TailTake.of.Gt_0]


-- created on 2025-07-06
-- updated on 2025-11-04
