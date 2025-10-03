import Lemma.List.Take.eq.Cons_TakeTail.of.GtLength_0.Gt_0
open List


@[main]
private lemma main
  [Mul α] [One α]
  {s : List α}
  {i : ℕ}
-- given
  (h : s.length > 0)
  (h_i : i > 0) :
-- imply
  (s.take i).prod = s[0] * (s.tail.take (i - 1)).prod := by
-- proof
  rw [Take.eq.Cons_TakeTail.of.GtLength_0.Gt_0 h_i h]
  simp


-- created on 2025-07-05
