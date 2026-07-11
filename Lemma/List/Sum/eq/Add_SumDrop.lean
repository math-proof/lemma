import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.List.SumCons.eq.Add_Sum
import Lemma.List.Tail.eq.Drop_1
open List


@[main]
private lemma main
  [Add α] [Zero α]
  {s : List α}
-- given
  (h : s.length > 0) :
-- imply
  s.sum = s[0] + (s.drop 1).sum := by
-- proof
  conv_lhs => rw [Eq_Cons_Tail.of.GtLength_0 h]
  rw [SumCons.eq.Add_Sum, Tail.eq.Drop_1]


-- created on 2026-07-11
