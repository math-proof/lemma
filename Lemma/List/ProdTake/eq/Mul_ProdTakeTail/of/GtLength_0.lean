import Lemma.List.Take.eq.Cons_TakeTail.of.Gt_0.GtLength_0
open List


@[main, comm]
private lemma main
  [Mul α] [One α]
  {s : List α}
-- given
  (h : s.length > 0)
  (i : ℕ) :
-- imply
  (s.take i.succ).prod = s[0] * (s.tail.take i).prod := by
-- proof
  simp [Take.eq.Cons_TakeTail.of.Gt_0.GtLength_0 h]


-- created on 2026-07-13
