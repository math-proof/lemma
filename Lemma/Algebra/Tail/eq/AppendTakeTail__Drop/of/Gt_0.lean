import Lemma.Algebra.Tail.eq.AppendTailTake__Drop.of.Gt_0
import Lemma.Algebra.TakeTail.eq.TailTake
import Lemma.Algebra.EqAddSub.of.Ge
open Algebra


@[main]
private lemma main
  {d : ℕ}
-- given
  (h : d > 0)
  (s : List α) :
-- imply
  s.tail = s.tail.take (d - 1) ++ s.drop d := by
-- proof
  have := Tail.eq.AppendTailTake__Drop.of.Gt_0 h s
  apply this.trans
  congr
  rw [TakeTail.eq.TailTake]
  rwa [EqAddSub.of.Ge]


-- created on 2025-07-06
